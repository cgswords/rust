// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Functions dealing with attributes and meta items

pub use self::StabilityLevel::*;
pub use self::ReprAttr::*;
pub use self::IntType::*;

use ast;
use ast::{AttrId, Attribute, Attribute_, ReifiedAttr, ReifiedAttr_};
use ast::{MetaItem, MetaItemKind, ReifiedMetaItem, ReifiedMetaItem_, reify_metaitem_list};
use ast::{Stmt, StmtKind, DeclKind};
use ast::{Expr, Item, Local, Decl};
use codemap::{Span, Spanned, spanned, dummy_spanned, mk_sp};
use codemap::BytePos;
use config::CfgDiag;
use errors::Handler;
use feature_gate::{GatedCfg, GatedCfgAttr};
use parse::lexer::comments::{doc_comment_style, strip_doc_comment_decoration};
use parse::token::InternedString;
use parse::token::{str_to_ident};
use parse::token;
use ptr::P;
use tokenstream;

use std::cell::{RefCell, Cell};
use std::collections::HashSet;
use std::collections::HashMap;


// For marking attributes as used by their IDs
thread_local! {
    static USED_ATTRS: RefCell<Vec<u64>> = RefCell::new(Vec::new())
}

pub fn mark_used(attr: &Attribute) {
    let AttrId(id) = attr.node.id;
    USED_ATTRS.with(|slot| {
        let idx = (id / 64) as usize;
        let shift = id % 64;
        if slot.borrow().len() <= idx {
            slot.borrow_mut().resize(idx + 1, 0);
        }
        slot.borrow_mut()[idx] |= 1 << shift;
    });
}

pub fn mark_reified_used(attr: &ReifiedAttr) {
    let AttrId(id) = 
      match (*attr).node {
        ReifiedAttr_::Word(id,_) | ReifiedAttr_::Assign(id,_,_) | ReifiedAttr_::List(id,_,_) => id
      };
    USED_ATTRS.with(|slot| {
        let idx = (id / 64) as usize;
        let shift = id % 64;
        if slot.borrow().len() <= idx {
            slot.borrow_mut().resize(idx + 1, 0);
        }
        slot.borrow_mut()[idx] |= 1 << shift;
    });
}

pub fn is_used(attr: &Attribute) -> bool {
    let AttrId(id) = attr.node.id;
    USED_ATTRS.with(|slot| {
        let idx = (id / 64) as usize;
        let shift = id % 64;
        slot.borrow().get(idx).map(|bits| bits & (1 << shift) != 0)
            .unwrap_or(false)
    })
}

pub fn is_reified_used(attr: &ReifiedAttr) -> bool {
    let AttrId(id) = 
      match (*attr).node {
        ReifiedAttr_::Word(id,_) | ReifiedAttr_::Assign(id,_,_) | ReifiedAttr_::List(id,_,_) => id
      };
    USED_ATTRS.with(|slot| {
        let idx = (id / 64) as usize;
        let shift = id % 64;
        slot.borrow().get(idx).map(|bits| bits & (1 << shift) != 0)
            .unwrap_or(false)
    })
}

// MetaMethods for inspecting reified attributes and reified metaitems.
pub trait AttrMetaMethods {
    fn check_name(&self, name: &str) -> bool {
        name == &self.name()[..]
    }

    /// Retrieve the name of the meta item, e.g. `foo` in `#[foo]`,
    /// `#[foo="bar"]` and `#[foo(bar)]`
    fn name(&self) -> InternedString;

    /// Gets the string value if self is a MetaItemKind::NameValue variant
    /// containing a string, otherwise None.
    fn value_str(&self) -> Option<InternedString>;
    /// Gets a list of inner meta items from a list MetaItem type.
    fn meta_item_list(&self) -> Option<&[P<MetaItem>]>;

    fn is_name(&self)   -> bool;
    fn is_assign(&self) -> bool;
    fn is_list(&self)   -> bool;

    fn maybe_word(&self)   -> Option<InternedString>;
    fn maybe_assign(&self) -> Option<(InternedString, InternedString)>;

    fn span(&self) -> Span;
}

impl AttrMetaMethods for Attribute {
    fn check_name(&self, name: &str) -> bool {
        let matches = name == &self.name()[..];
        if matches {
            mark_used(self);
        }
        matches
    }

    fn name(&self) -> InternedString {
      self.node.path.get_last_ident().name.as_str() 
    }

    fn value_str(&self) -> Option<InternedString> {
      if let Some(ra) = self.to_reified_attr() {
        ra.value_str()
      } else {
        None 
      }
    }

    fn meta_item_list(&self) -> Option<&[P<MetaItem>]> {
      if let Some(ra) = self.to_reified_attr() {
        ra.meta_item_list()
      } else {
        None
      }
    }

    fn is_name(&self) -> bool {
      if self.node.stream.is_empty() {
        true
      } else { false }
    }
    
    fn is_assign(&self) -> bool { 
      if self.node.stream.is_assignment() {
        true
      } else { false }
    }
    
    fn is_list(&self) -> bool { 
      if self.node.stream.is_delimited() {
        true
      } else { false }
    }
 
    fn maybe_word(&self) -> Option<InternedString> {
      if let Some(ra) = self.to_reified_attr() {
        ra.maybe_word()
      } else {
        None
      }
    }

    fn maybe_assign(&self) -> Option<(InternedString, InternedString)> {
      if let Some(ra) = self.to_reified_attr() {
        ra.maybe_assign()
      } else {
        None
      }
    }

    fn span(&self) -> Span { self.span }
}

impl AttrMetaMethods for ReifiedAttr {
    fn check_name(&self, name: &str) -> bool {
        let matches = name == &self.name()[..];
        if matches {
            mark_reified_used(self);
        }
        matches
    }

    fn name(&self) -> InternedString { 
      match self.node {
        ReifiedAttr_::Word(_,p) | ReifiedAttr_::Assign(_,p,_) | ReifiedAttr_::List(_,p,_) 
          => p.get_last_ident().name.as_str()
      }
    }

    fn value_str(&self) -> Option<InternedString> {
      match self.node {
        ReifiedAttr_::Assign(_,_,ref  v) => {
          match v.node {
            ast::LitKind::Str(ref s, _) => Some((*s).clone()),
            _ => None,
          }
        }
        _ => None
      }
    }

    fn meta_item_list(&self) -> Option<&[P<MetaItem>]> {
      match self.node {
      ReifiedAttr_::List(_,_, mi) => {
        let mis = mi.iter().map(|&x| P(x)).collect::<Vec<P<MetaItem>>>();
        Some(&mis[..])
      }
      _ => None 
      }
    }

    fn is_name(&self) -> bool { 
      match self.node
        { ReifiedAttr_::Word(_,_) => true
        , _ => false
        }
    }
    
    fn is_assign(&self) -> bool { 
      match self.node
        { ReifiedAttr_::Assign(_,_,_) => true
        , _ => false
        }
    }
    
    fn is_list(&self) -> bool { 
      match self.node
        { ReifiedAttr_::List(_,_,_) => true
        , _ => false
        }
    }
 
    fn maybe_word(&self) -> Option<InternedString> {
      match self.node {
        ReifiedAttr_::Word(_,ref n) => Some(self.name()),
        _ => None
      }
    }

    fn maybe_assign(&self) -> Option<(InternedString, InternedString)> {
      let name = self.name();
      let val = self.value_str();
      match val
        { Some(v) => Some((name, v)) 
        , _ => None 
        }
    }

    fn span(&self) -> Span { self.span }
}

impl AttrMetaMethods for MetaItem {
    fn check_name(&self, name: &str) -> bool {
      let matches = name == &self.name()[..];
      matches
    }

    fn name(&self) -> InternedString {
      self.node.name
    }

    fn value_str(&self) -> Option<InternedString> {
      if let Some(ra) = self.to_reified_metaitem() {
        ra.value_str()
      } else {
        None
      }
    }

    fn meta_item_list(&self) -> Option<&[P<MetaItem>]> {
      if let Some(ra) = self.to_reified_metaitem() {
        ra.meta_item_list()
      } else {
        None
      }
    }

    fn is_name(&self) -> bool {
      if self.node.stream.is_empty() {
        true
      } else { false }
    }
    
    fn is_assign(&self) -> bool { 
      if self.node.stream.is_assignment() {
        true
      } else { false }
    }
    
    fn is_list(&self) -> bool { 
      if self.node.stream.is_delimited() {
        true
      } else { false }
    }
 
    fn maybe_word(&self) -> Option<InternedString> {
      if let Some(ra) = self.to_reified_metaitem() {
        ra.maybe_word()
      } else {
        None
      }
    }

    fn maybe_assign(&self) -> Option<(InternedString, InternedString)> {
      if let Some(ra) = self.to_reified_metaitem() {
        ra.maybe_assign()
      } else {
        None
      }
    }

    fn span(&self) -> Span { self.span }
}

impl AttrMetaMethods for ReifiedMetaItem {
    fn name(&self) -> InternedString {
      match self.node {
        ReifiedMetaItem_::Word(ref n) => (*n).clone(),
        ReifiedMetaItem_::Assign(ref n, _) => (*n).clone(),
        ReifiedMetaItem_::List(ref n, _) => (*n).clone(),
      }
    }

    fn value_str(&self) -> Option<InternedString> {
      match self.node {
        ReifiedMetaItem_::Assign(_, ref v) => {
          match v.node {
            ast::LitKind::Str(ref s, _) => Some((*s).clone()),
            _ => None,
          }
        },
        _ => None
      }
    }

    fn meta_item_list(&self) -> Option<&[P<MetaItem>]> {
      match self.node {
        ReifiedMetaItem_::List(_, mi) => {
          let mis = mi.iter().map(|&x| P(x)).collect::<Vec<P<MetaItem>>>();
          Some(&mis[..])
        }
        _ => None
      }
    }

    fn is_name(&self) -> bool { 
      match self.node
        { ReifiedMetaItem_::Word(_) => true
        , _ => false
        }
    }
    
    fn is_assign(&self) -> bool { 
      match self.node
        { ReifiedMetaItem_::Assign(_,_) => true
        , _ => false
        }
    }
    
    fn is_list(&self) -> bool { 
      match self.node
        { ReifiedMetaItem_::List(_,_) => true
        , _ => false
        }
    }

    fn maybe_word(&self) -> Option<InternedString> {
      match self.node {
        ReifiedMetaItem_::Word(ref n) => Some((*n).clone()),
        _ => None
      }
    }

    fn maybe_assign(&self) -> Option<(InternedString, InternedString)> {
      let name = self.name();
      let val = self.value_str();
      match val
        { Some(v) => Some((name, v)) 
        , _ => None 
        }
    }

    fn span(&self) -> Span { self.span }
}

// These next two are annoying, but required
impl AttrMetaMethods for P<ReifiedMetaItem> {
    fn name(&self) -> InternedString { (**self).name() }
    fn value_str(&self) -> Option<InternedString> { (**self).value_str() }
    fn meta_item_list(&self) -> Option<&[P<MetaItem>]> {
        (**self).meta_item_list()
    }
    fn is_name(&self)   -> bool { (**self).is_name() }
    fn is_assign(&self) -> bool { (**self).is_assign() }
    fn is_list(&self)   -> bool { (**self).is_list() }

    fn maybe_word(&self)   -> Option<InternedString> { (**self).maybe_word() }
    fn maybe_assign(&self) -> Option<(InternedString, InternedString)> 
    { (**self).maybe_assign() }

    fn span(&self) -> Span { (**self).span() }
}

impl AttrMetaMethods for P<MetaItem> {
    fn name(&self) -> InternedString { (**self).name() }
    fn value_str(&self) -> Option<InternedString> { (**self).value_str() }
    fn meta_item_list(&self) -> Option<&[P<MetaItem>]> {
        (**self).meta_item_list()
    }
    fn is_name(&self)   -> bool { (**self).is_name() }
    fn is_assign(&self) -> bool { (**self).is_assign() }
    fn is_list(&self)   -> bool { (**self).is_list() }

    fn maybe_word(&self)   -> Option<InternedString> { (**self).maybe_word() }
    fn maybe_assign(&self) -> Option<(InternedString, InternedString)> 
    { (**self).maybe_assign() }

    fn span(&self) -> Span { (**self).span() }
}



//-----------------------------------------------------------------------------------
//-----------------------------------------------------------------------------------
// TODO: FIX ALL OF THIS
/*
pub trait AttributeMethods {
fn with_desugared_doc<T, F>(&self, f: F) -> T where
        F: FnOnce(&Attribute) -> T;
}

impl AttributeMethods for Attribute {
    /// Convert self to a normal #[doc="foo"] comment, if it is a
    /// comment like `///` or `/** */`. (Returns self unchanged for
    /// non-sugared doc attributes.)
    fn with_desugared_doc<T, F>(&self, f: F) -> T where
        F: FnOnce(&Attribute) -> T,
    {
        if self.node.is_sugared_doc {
            let comment = self.value_str().unwrap();
            let meta = mk_name_value_item_str(
                InternedString::new("doc"),
                token::intern_and_get_ident(&strip_doc_comment_decoration(
                        &comment)));
            if self.node.style == ast::AttrStyle::Outer {
                f(&mk_attr_outer(self.node.id, meta))
            } else {
                f(&mk_attr_inner(self.node.id, meta))
            }
        } else {
            f(self)
        }
    }
}
*/
/* Constructors */

pub fn mk_name_value_item_str(name: InternedString, value: InternedString)
                              -> P<MetaItem> {
  let value_lit = dummy_spanned(ast::LitKind::Str(value, ast::StrStyle::Cooked));
  P(dummy_spanned(MetaItemKind { name   : name
                               , stream : tokenstream::TokenStream::from_ast_lit_str(value_lit)
                               }))
}

// pub fn mk_name_value_item(name: InternedString, value: ast::Lit)
//                           -> P<MetaItem> {
//     P(dummy_spanned(MetaItemKind::NameValue(name, value)))
// }

pub fn mk_list_item(name: InternedString, items: Vec<MetaItem>) -> P<MetaItem> {
  P(dummy_spanned(MetaItemKind { name : name
                               , stream : ReifiedMetaItem::recover_vec_tokenstream(items) }))
}

pub fn mk_word_item(name: InternedString) -> P<MetaItem> {
  P(dummy_spanned(MetaItemKind { name : name
                               , stream : tokenstream::tts_to_ts(vec![])
                               }))
}


//-----------------------------------------------------------------------------------
//-----------------------------------------------------------------------------------

// Setting up structures for attribute IDs to track their usages.
thread_local! { static NEXT_ATTR_ID: Cell<usize> = Cell::new(0) }

pub fn mk_attr_id() -> AttrId {
    let id = NEXT_ATTR_ID.with(|slot| {
        let r = slot.get();
        slot.set(r + 1);
        r
    });
    AttrId(id)
}

/// Returns an inner attribute with the given value.
pub fn mk_attr_inner(id: AttrId, item: P<ReifiedAttr>) -> Attribute {
  dummy_spanned(Attribute_ {
      id: id,
      style: ast::AttrStyle::Inner,
      path : (*item).path(),  
      stream: (*item).recover_tokenstream(),
      is_sugared_doc: false,
  })
}

/// Returns an outer attribute with the given value.
pub fn mk_attr_outer(id: AttrId, item: P<ReifiedAttr>) -> Attribute {
    dummy_spanned(Attribute_ {
        id: id,
        style: ast::AttrStyle::Outer,
        path : (*item).path(),  
        stream: (*item).recover_tokenstream(),
        is_sugared_doc: false,
    })
}

pub fn mk_sugared_doc_attr(id: AttrId, text: InternedString, lo: BytePos,
                           hi: BytePos)
                           -> Attribute {
    let style = doc_comment_style(&text);
    let lit = spanned(lo, hi, ast::LitKind::Str(text, ast::StrStyle::Cooked));
    let attr = Attribute_ {
        id: id,
        style: style,
        path : ast::Path::from_ident(mk_sp(lo, hi), str_to_ident("doc")),
        stream : tokenstream::TokenStream::from_ast_lit_str(lit),
        is_sugared_doc: true
    };
    spanned(lo, hi, attr)
}

fn pretty_print_args(args: &[&str]) -> String {
  let mut comma_sep = String::new();
	
  comma_sep.push_str("'");
  comma_sep.push_str(args[0]);
  comma_sep.push_str("'");

	for arg in args.into_iter().skip(1) {
    comma_sep.push_str(", '");
    comma_sep.push_str(arg);
  comma_sep.push_str("'");
  }
	
	comma_sep
}

/* Searchin (via heapify) */
/// Converts the Reified MetaItems into a HashMap that contains the expected names.
/// If the items contain extra names or duplicates, diagnostics receives an error instead.
fn to_assign_map(diagnostic: &Handler, expected_names : &[&str], metas : &[ReifiedMetaItem]) 
                 -> Option<HashMap<String, InternedString>> {
  let mut metamap : HashMap<String, InternedString> = HashMap::new();

  for meta in metas {
    if !expected_names.contains(&(&meta.name()[..])) {
      diagnostic.span_err(meta.span, 
                          &format!("incorrect attribute item '{}', expected items {}", 
																	 meta.name(), 
																	 pretty_print_args(expected_names)));
      return None;
    }
    if let Some((name, lit)) = meta.maybe_assign() {
      let name = (&*name).to_string();
      if metamap.contains_key(&name) {
        diagnostic.span_err(meta.span, &format!("multiple '{}' items", meta.name())); 
        return None;
      }
      metamap.insert(name, lit);
    } else {
      diagnostic.span_err(meta.span, 
                          &format!("incorrect attribute format for '{}', \
                                    expected '{} = \"value\"'", 
                                   meta.name(), meta.name()));
      return None;
    }
  }

  Some(metamap)
}

/* Searching */
/// Check if `needle` occurs in `haystack` by a structural
/// comparison. This is slightly subtle, and relies on ignoring the
/// span included in the `==` comparison a plain MetaItem.
pub fn contains(haystack: &[P<MetaItem>], needle: &MetaItem) -> bool {
    debug!("attr::contains (name={})", needle.name());
    haystack.iter().any(|&item| {
        debug!("  testing: {}", item.name());
        item.node == needle.node
    })
}

pub fn contains_name<AM: AttrMetaMethods>(metas: &[AM], name: &str) -> bool {
    debug!("attr::contains_name (name={})", name);
    metas.iter().any(|item| {
        debug!("  testing: {}", item.name());
        item.check_name(name)
    })
}

pub fn first_attr_value_str_by_name(attrs: &[Attribute], name: &str)
                                 -> Option<InternedString> {
    attrs.iter()
         .find(|at| at.check_name(name))
         .and_then(|at| at.value_str())
}

// This never gets called
// pub fn last_meta_item_value_str_by_name(items: &[P<MetaItem>], name: &str)
//                                      -> Option<InternedString> {
//     items.iter()
//          .rev()
//          .find(|mi| mi.check_name(name))
//          .and_then(|i| i.value_str())
// }

/* Higher-level applications */

// This never gets called
// pub fn sort_meta_items(items: Vec<P<MetaItem>>) -> Vec<P<MetaItem>> {
//     // This is sort of stupid here, but we need to sort by
//     // human-readable strings.
//     let mut v = items.into_iter()
//         .map(|mi| (mi.name(), mi))
//         .collect::<Vec<(InternedString, P<MetaItem>)>>();
// 
//     v.sort_by(|&(ref a, _), &(ref b, _)| a.cmp(b));
// 
//     // There doesn't seem to be a more optimal way to do this
//     v.into_iter().map(|(_, m)| m.map(|Spanned {node, span}| {
//         Spanned {
//             node: match node {
//                 MetaItemKind::List(n, mis) => MetaItemKind::List(n, sort_meta_items(mis)),
//                 _ => node
//             },
//             span: span
//         }
//     })).collect()
// }

pub fn find_crate_name(attrs: &[Attribute]) -> Option<InternedString> {
    first_attr_value_str_by_name(attrs, "crate_name")
}

/// Find the value of #[export_name=*] attribute and check its validity.
pub fn find_export_name_attr(diag: &Handler, attrs: &[Attribute]) -> Option<InternedString> {
    attrs.iter().fold(None, |ia,attr| {
        if attr.check_name("export_name") {
            if let s@Some(_) = attr.value_str() {
                s
            } else {
                diag.struct_span_err(attr.span,
                                     "export_name attribute has invalid format")
                    .help("use #[export_name=\"*\"]")
                    .emit();
                None
            }
        } else {
            ia
        }
    })
}

pub fn contains_extern_indicator(diag: &Handler, attrs: &[Attribute]) -> bool {
    contains_name(attrs, "no_mangle") ||
        find_export_name_attr(diag, attrs).is_some()
}

#[derive(Copy, Clone, PartialEq)]
pub enum InlineAttr {
    None,
    Hint,
    Always,
    Never,
}

/// Determine what `#[inline]` attribute is present in `attrs`, if any.
pub fn find_inline_attr(diagnostic: Option<&Handler>, attrs: &[Attribute]) -> InlineAttr {
    attrs.iter().fold(InlineAttr::None, |ia,attr| {
        if attr.is_name() && attr.check_name("inline") {
           mark_used(attr);
           InlineAttr::Hint
        } else if attr.is_list() && attr.check_name("inline") {
          mark_used(attr);
          if let Some(items) = attr.meta_item_list() {
            if items.len() != 1 {
              diagnostic.map(|d|{ d.span_err(attr.span, "expected one argument"); });
              InlineAttr::None
            } else if contains_name(&items[..], "always") {
              InlineAttr::Always
            } else if contains_name(&items[..], "never") {
              InlineAttr::Never
            } else {
              diagnostic.map(|d|{ d.span_err((*items[0]).span, "invalid argument"); });
              InlineAttr::None
            }
          } else {
            diagnostic.map(|d|{ d.span_err(attr.span, "The compiler detected an attribute list but could not retrieve one"); });
            InlineAttr::None
          }
        } else if attr.is_assign() && attr.check_name("inline") {
            diagnostic.map(|d|{ d.span_err(attr.span, "illegal inline syntax (no assignments allowed)"); });
            ia
        } else {
          ia
        } 
    })
}

/// True if `#[inline]` or `#[inline(always)]` is present in `attrs`.
pub fn requests_inline(attrs: &[Attribute]) -> bool {
    match find_inline_attr(None, attrs) {
        InlineAttr::Hint | InlineAttr::Always => true,
        InlineAttr::None | InlineAttr::Never => false,
    }
}


// TODO Sort what this thing is actually doing.
/// Tests if a cfg-pattern matches the cfg set
pub fn cfg_matches<T: CfgDiag>(cfgs: &[P<MetaItem>],
                           cfg: &ast::MetaItem,
                           diag: &mut T) -> bool {
  if cfg.is_list() {
    let name = cfg.name();
      if let Some(items) = cfg.meta_item_list() {
        match &name[..] 
          { "any" => items.iter().any(|mi| cfg_matches(cfgs, &mi, diag))
          , "all" => items.iter().all(|mi| cfg_matches(cfgs, &mi, diag))
          , "not" => { 
             if items.len() != 1 {
                diag.emit_error(|diagnostic| {
                    diagnostic.span_err(cfg.span, "expected 1 cfg-pattern");
                });
                return false;
              } 
              !cfg_matches(cfgs, &items[0], diag)
            }
          ,_ => {
              diag.emit_error(|diagnostic| {
                diagnostic.span_err(cfg.span,
                  &format!("invalid predicate `{}`", name));
               });
              false
            }
          }
      } else {
        diag.emit_error(|diagnostic| {
          diagnostic.span_err(cfg.span,
            &format!("invalid attribute form `{:?}`", cfg));
         });
       false
     }
  } else if cfg.is_name() || cfg.is_assign() {
    diag.flag_gated(|feature_gated_cfgs| {
      feature_gated_cfgs.extend(
        GatedCfg::gate(cfg).map(GatedCfgAttr::GatedCfg));
    });
    contains(cfgs, cfg)
  } else {
    diag.emit_error(|diagnostic| {
      diagnostic.span_err(cfg.span, &format!("Invalid metaitem `{:?}`", cfg));
    });
    false
  }
}

/// Represents the #[stable], #[unstable] and #[rustc_deprecated] attributes.
#[derive(RustcEncodable, RustcDecodable, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Stability {
    pub level: StabilityLevel,
    pub feature: InternedString,
    pub rustc_depr: Option<RustcDeprecation>,
}

/// The available stability levels.
#[derive(RustcEncodable, RustcDecodable, PartialEq, PartialOrd, Clone, Debug, Eq, Hash)]
pub enum StabilityLevel {
    // Reason for the current stability level and the relevant rust-lang issue
    Unstable { reason: Option<InternedString>, issue: u32 },
    Stable { since: InternedString },
}

#[derive(RustcEncodable, RustcDecodable, PartialEq, PartialOrd, Clone, Debug, Eq, Hash)]
pub struct RustcDeprecation {
    pub since: InternedString,
    pub reason: InternedString,
}

#[derive(RustcEncodable, RustcDecodable, PartialEq, PartialOrd, Clone, Debug, Eq, Hash)]
pub struct Deprecation {
    pub since: Option<InternedString>,
    pub note: Option<InternedString>,
}

impl StabilityLevel {
    pub fn is_unstable(&self) -> bool { if let Unstable {..} = *self { true } else { false }}
    pub fn is_stable(&self) -> bool { if let Stable {..} = *self { true } else { false }}
}

fn find_stability_generic<'a, I>(diagnostic: &Handler,
                                 attrs_iter: I,
                                 item_sp: Span)
                                 -> Option<Stability>
    where I: Iterator<Item = &'a Attribute>
{
    let mut stab: Option<Stability> = None;
    let mut rustc_depr: Option<RustcDeprecation> = None;

    'outer: for attr in attrs_iter {
        let tag = attr.name();
        let tag = &*tag;
        if tag != "rustc_deprecated" && tag != "unstable" && tag != "stable" {
            continue // not a stability level
        }

        let rattr = attr.to_reified_attr();
        if rattr.is_none() {
            diagnostic.span_err(attr.span(), &format!("invalid attribute '{:?}'", attr));
            continue 'outer
        }
        let attr = rattr.unwrap();
        mark_reified_used(&attr);

        if let Some(metas) = attr.meta_item_list() {
          let rmetas = reify_metaitem_list(metas);
          if rmetas.is_none() { 
            diagnostic.span_err(attr.span(), &format!("invalid argument list for '{:?}'", attr));
            continue 'outer
          }
          let metas = rmetas.unwrap();
          match tag {
            "rustc_deprecated" => {
              if rustc_depr.is_some() {
                diagnostic.span_err(item_sp, "multiple rustc_deprecated attributes");
                break
              }
              if let Some(mut map) = to_assign_map(diagnostic,&["since", "reason"],&metas) {
                let since  = map.remove("since");
                let reason = map.remove("reason");
                match (since, reason) {
                  (Some(since), Some(reason)) => {
                    rustc_depr = Some(RustcDeprecation { since  : since, reason : reason });
                  }
                  (None, _) => {
                    diagnostic.span_err(attr.span(), "missing 'since'"); 
                    continue 'outer
                  }
                  _ => {
                    diagnostic.span_err(attr.span(), "missing 'reason'"); 
                    continue 'outer
                  }
                }
              } else { // to_assign_map has already produced the necessary diagnostic information
                continue 'outer
              }
            }
            "unstable" => {
              if stab.is_some() {
                diagnostic.span_err(item_sp, "multiple stability levels");
                break
              }
              if let Some(mut map) = to_assign_map(diagnostic,&["feature", "reason", "issue"],&metas) {
                let feature = map.remove("feature");
                let reason  = map.remove("reason");
                let issue   = map.remove("issue");
                match (feature, reason, issue) {
                  (Some(feature), reason, Some(issue)) => {
                    if let Ok(issue) = issue.parse() {
                      stab = Some(Stability { level      : Unstable { reason : reason
                                                                    , issue  : issue }
                                            , feature    : feature
                                            , rustc_depr : None});
                    } else {
                      diagnostic.span_err(attr.span(), "incorrect 'issue'"); 
                      continue 'outer
                    }
                  }
                  (None, _, _) => {
                    diagnostic.span_err(attr.span(), "missing 'feature'"); 
                    continue 'outer
                  }
                  _ => {
                    diagnostic.span_err(attr.span(), "missing 'issue'"); 
                    continue 'outer
                  }
                }
              } else { // to_assign_map has already produced the necessary diagnostic information
                continue 'outer
              }
            }
            "stable" => {
              if stab.is_some() {
                diagnostic.span_err(item_sp, "multiple stability levels");
                break
              }
              if let Some(mut map) = to_assign_map(diagnostic,&["feature", "since"],&metas) {
                let feature = map.remove("feature");
                let since   = map.remove("since");
                match (feature, since) {
                  (Some(feature),Some(since)) => {
                    stab = Some(Stability { level      : Stable { since : since }
                                          , feature    : feature
                                          , rustc_depr : None})
                  }
                  (None, _) => {
                    diagnostic.span_err(attr.span(), "missing 'feature'"); 
                    continue 'outer
                  }
                  _ => {
                    diagnostic.span_err(attr.span(), "missing 'since'"); 
                    continue 'outer
                  }
                }
              } else { // to_assign_map has already produced the necessary diagnostic information
                continue 'outer
              }

            }
            _ => unreachable!()
          }
        } else {
          diagnostic.span_err(attr.span(), "incorrect stability attribute type");
          continue
        }
    }
    // Merge the deprecation info into the stability info
    if let Some(rustc_depr) = rustc_depr {
        if let Some(ref mut stab) = stab {
            if let Unstable {reason: ref mut reason @ None, ..} = stab.level {
                *reason = Some(rustc_depr.reason.clone())
            }
            stab.rustc_depr = Some(rustc_depr);
        } else {
            diagnostic.span_err(item_sp, "rustc_deprecated attribute must be paired with \
                                          either stable or unstable attribute");
        }
    }

    stab
}

fn find_deprecation_generic<'a, I>(diagnostic: &Handler,
                                   attrs_iter: I,
                                   item_sp: Span)
                                   -> Option<Deprecation>
    where I: Iterator<Item = &'a Attribute>
{
  let mut depr: Option<Deprecation> = None;

  'outer: for attr in attrs_iter {
    if attr.name() != "deprecated" {
        continue
    }

    let rattr = attr.to_reified_attr();
    if rattr.is_none() {
        diagnostic.span_err(attr.span(), &format!("invalid attribute '{:?}'", attr));
        continue 'outer
    }
    let attr = rattr.unwrap();
    mark_reified_used(&attr);

    if depr.is_some() {
        diagnostic.span_err(item_sp, "multiple deprecated attributes");
        break
    }

    if let Some(metas) = attr.meta_item_list() {
      let rmetas = reify_metaitem_list(metas);
      if rmetas.is_none() { 
        diagnostic.span_err(attr.span(), &format!("invalid argument list for '{:?}'", attr));
        continue 'outer
      }
      let metas = rmetas.unwrap();
    
      if let Some(mut map) = to_assign_map(diagnostic,&["since", "note"],&metas) {
        let since = map.remove("since");
        let note  = map.remove("note");
        depr = Some(Deprecation {since : since, note : note});
      } else { // to_assign_map has already produced the necessary diagnostic information
        continue 'outer
      }
    }
  }  
  depr
}

/// Find the first stability attribute. `None` if none exists.
pub fn find_stability(diagnostic: &Handler, attrs: &[Attribute],
                      item_sp: Span) -> Option<Stability> {
    find_stability_generic(diagnostic, attrs.iter(), item_sp)
}

/// Find the deprecation attribute. `None` if none exists.
pub fn find_deprecation(diagnostic: &Handler, attrs: &[Attribute],
                        item_sp: Span) -> Option<Deprecation> {
    find_deprecation_generic(diagnostic, attrs.iter(), item_sp)
}

pub fn require_unique_names(diagnostic: &Handler, metas: &[P<MetaItem>]) {
    let mut set = HashSet::new();
    for meta in metas {
        let name = meta.name();

        if !set.insert(name.clone()) {
            panic!(diagnostic.span_fatal(meta.span,
                                  &format!("duplicate meta item `{}`", name)));
        }
    }
}


/// Parse #[repr(...)] forms.
///
/// Valid repr contents: any of the primitive integral type names (see
/// `int_type_of_word`, below) to specify enum discriminant type; `C`, to use
/// the same discriminant size that the corresponding C enum would or C
/// structure layout, and `packed` to remove padding.
pub fn find_repr_attrs(diagnostic: &Handler, attr: &Attribute) -> Vec<ReprAttr> {
  let mut acc = Vec::new();
  if attr.is_list() && attr.check_name("repr") { 
    let items = attr.meta_item_list().unwrap();
    mark_used(attr);
    for item in items {
      if let Some(word) = item.maybe_word() {
        let hint = match &word[..] // Can't use "extern" because it's not a lexical identifier.
          { "C"      => Some(ReprExtern)
          , "packed" => Some(ReprPacked)
          , "simd"   => Some(ReprSimd)
          , _        => match int_type_of_word(&word) 
                          { Some(ity) => Some(ReprInt(item.span, ity))
                          , None => { // Not a word we recognize
                              diagnostic.span_err(item.span,
                                                  "unrecognized representation hint");
                              None
                            }
                          }
          };
        match hint {
          Some(h) => acc.push(h),
          None    => { }
        }
      } else { // Not a word:
        diagnostic.span_err(item.span, "unrecognized enum representation hint")
      }
    }
  }
  acc
}

fn int_type_of_word(s: &str) -> Option<IntType> {
  match s 
    { "i8"    => Some(SignedInt(ast::IntTy::I8))
    , "u8"    => Some(UnsignedInt(ast::UintTy::U8))
    , "i16"   => Some(SignedInt(ast::IntTy::I16))
    , "u16"   => Some(UnsignedInt(ast::UintTy::U16))
    , "i32"   => Some(SignedInt(ast::IntTy::I32))
    , "u32"   => Some(UnsignedInt(ast::UintTy::U32))
    , "i64"   => Some(SignedInt(ast::IntTy::I64))
    , "u64"   => Some(UnsignedInt(ast::UintTy::U64))
    , "isize" => Some(SignedInt(ast::IntTy::Is))
    , "usize" => Some(UnsignedInt(ast::UintTy::Us))
    , _       => None
    }
}

#[derive(PartialEq, Debug, RustcEncodable, RustcDecodable, Copy, Clone)]
pub enum ReprAttr {
    ReprAny,
    ReprInt(Span, IntType),
    ReprExtern,
    ReprPacked,
    ReprSimd,
}

impl ReprAttr {
    pub fn is_ffi_safe(&self) -> bool {
        match *self {
            ReprAny => false,
            ReprInt(_sp, ity) => ity.is_ffi_safe(),
            ReprExtern => true,
            ReprPacked => false,
            ReprSimd => true,
        }
    }
}

#[derive(Eq, Hash, PartialEq, Debug, RustcEncodable, RustcDecodable, Copy, Clone)]
pub enum IntType {
    SignedInt(ast::IntTy),
    UnsignedInt(ast::UintTy)
}

impl IntType {
    #[inline]
    pub fn is_signed(self) -> bool {
        match self {
            SignedInt(..) => true,
            UnsignedInt(..) => false
        }
    }
    fn is_ffi_safe(self) -> bool {
        match self {
            SignedInt(ast::IntTy::I8)  | UnsignedInt(ast::UintTy::U8)  |
            SignedInt(ast::IntTy::I16) | UnsignedInt(ast::UintTy::U16) |
            SignedInt(ast::IntTy::I32) | UnsignedInt(ast::UintTy::U32) |
            SignedInt(ast::IntTy::I64) | UnsignedInt(ast::UintTy::U64) => true,
            SignedInt(ast::IntTy::Is)  | UnsignedInt(ast::UintTy::Us)  => false
        }
    }
}

/// A list of attributes, behind a optional box as
/// a space optimization.
pub type ThinAttributes = Option<Box<Vec<Attribute>>>;

pub trait ThinAttributesExt {
    fn map_thin_attrs<F>(self, f: F) -> Self
        where F: FnOnce(Vec<Attribute>) -> Vec<Attribute>;
    fn prepend(mut self, attrs: Self) -> Self;
    fn append(mut self, attrs: Self) -> Self;
    fn update<F>(&mut self, f: F)
        where Self: Sized,
              F: FnOnce(Self) -> Self;
    fn as_attr_slice(&self) -> &[Attribute];
    fn into_attr_vec(self) -> Vec<Attribute>;
}

impl ThinAttributesExt for ThinAttributes {
    fn map_thin_attrs<F>(self, f: F) -> Self
        where F: FnOnce(Vec<Attribute>) -> Vec<Attribute>
    {
        f(self.map(|b| *b).unwrap_or(Vec::new())).into_thin_attrs()
    }

    fn prepend(self, attrs: ThinAttributes) -> Self {
        attrs.map_thin_attrs(|mut attrs| {
            attrs.extend(self.into_attr_vec());
            attrs
        })
    }

    fn append(self, attrs: ThinAttributes) -> Self {
        self.map_thin_attrs(|mut self_| {
            self_.extend(attrs.into_attr_vec());
            self_
        })
    }

    fn update<F>(&mut self, f: F)
        where Self: Sized,
              F: FnOnce(ThinAttributes) -> ThinAttributes
    {
        let self_ = f(self.take());
        *self = self_;
    }

    fn as_attr_slice(&self) -> &[Attribute] {
        match *self {
            Some(ref b) => b,
            None => &[],
        }
    }

    fn into_attr_vec(self) -> Vec<Attribute> {
        match self {
            Some(b) => *b,
            None => Vec::new(),
        }
    }
}

pub trait AttributesExt {
    fn into_thin_attrs(self) -> ThinAttributes;
}

impl AttributesExt for Vec<Attribute> {
    fn into_thin_attrs(self) -> ThinAttributes {
        if self.len() == 0 {
            None
        } else {
            Some(Box::new(self))
        }
    }
}

pub trait HasAttrs: Sized {
    fn attrs(&self) -> &[ast::Attribute];
    fn map_attrs<F: FnOnce(Vec<ast::Attribute>) -> Vec<ast::Attribute>>(self, f: F) -> Self;
}

/// A cheap way to add Attributes to an AST node.
pub trait WithAttrs {
    // FIXME: Could be extended to anything IntoIter<Item=Attribute>
    fn with_attrs(self, attrs: ThinAttributes) -> Self;
}

impl<T: HasAttrs> WithAttrs for T {
    fn with_attrs(self, attrs: ThinAttributes) -> Self {
        self.map_attrs(|mut orig_attrs| {
            orig_attrs.extend(attrs.into_attr_vec());
            orig_attrs
        })
    }
}

impl HasAttrs for Vec<Attribute> {
    fn attrs(&self) -> &[Attribute] {
        &self
    }
    fn map_attrs<F: FnOnce(Vec<Attribute>) -> Vec<Attribute>>(self, f: F) -> Self {
        f(self)
    }
}

impl HasAttrs for ThinAttributes {
    fn attrs(&self) -> &[Attribute] {
        self.as_attr_slice()
    }
    fn map_attrs<F: FnOnce(Vec<Attribute>) -> Vec<Attribute>>(self, f: F) -> Self {
        self.map_thin_attrs(f)
    }
}

impl<T: HasAttrs + 'static> HasAttrs for P<T> {
    fn attrs(&self) -> &[Attribute] {
        (**self).attrs()
    }
    fn map_attrs<F: FnOnce(Vec<Attribute>) -> Vec<Attribute>>(self, f: F) -> Self {
        self.map(|t| t.map_attrs(f))
    }
}

impl HasAttrs for DeclKind {
    fn attrs(&self) -> &[Attribute] {
        match *self {
            DeclKind::Local(ref local) => local.attrs(),
            DeclKind::Item(ref item) => item.attrs(),
        }
    }

    fn map_attrs<F: FnOnce(Vec<Attribute>) -> Vec<Attribute>>(self, f: F) -> Self {
        match self {
            DeclKind::Local(local) => DeclKind::Local(local.map_attrs(f)),
            DeclKind::Item(item) => DeclKind::Item(item.map_attrs(f)),
        }
    }
}

impl HasAttrs for StmtKind {
    fn attrs(&self) -> &[Attribute] {
        match *self {
            StmtKind::Decl(ref decl, _) => decl.attrs(),
            StmtKind::Expr(ref expr, _) | StmtKind::Semi(ref expr, _) => expr.attrs(),
            StmtKind::Mac(_, _, ref attrs) => attrs.attrs(),
        }
    }

    fn map_attrs<F: FnOnce(Vec<Attribute>) -> Vec<Attribute>>(self, f: F) -> Self {
        match self {
            StmtKind::Decl(decl, id) => StmtKind::Decl(decl.map_attrs(f), id),
            StmtKind::Expr(expr, id) => StmtKind::Expr(expr.map_attrs(f), id),
            StmtKind::Semi(expr, id) => StmtKind::Semi(expr.map_attrs(f), id),
            StmtKind::Mac(mac, style, attrs) =>
                StmtKind::Mac(mac, style, attrs.map_attrs(f)),
        }
    }
}

macro_rules! derive_has_attrs_from_field {
    ($($ty:path),*) => { derive_has_attrs_from_field!($($ty: .attrs),*); };
    ($($ty:path : $(.$field:ident)*),*) => { $(
        impl HasAttrs for $ty {
            fn attrs(&self) -> &[Attribute] {
                self $(.$field)* .attrs()
            }

            fn map_attrs<F>(mut self, f: F) -> Self
                where F: FnOnce(Vec<Attribute>) -> Vec<Attribute>,
            {
                self $(.$field)* = self $(.$field)* .map_attrs(f);
                self
            }
        }
    )* }
}

derive_has_attrs_from_field! {
    Item, Expr, Local, ast::ForeignItem, ast::StructField, ast::ImplItem, ast::TraitItem, ast::Arm
}

derive_has_attrs_from_field! { Decl: .node, Stmt: .node, ast::Variant: .node.attrs }
