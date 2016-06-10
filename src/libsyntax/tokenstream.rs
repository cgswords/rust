// Copyright 2012-2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use ast::{self, AttrStyle, LitKind, MetaItemKind};
use codemap::{self, Span, mk_sp, Spanned, DUMMY_SP};
use ext::base;
use ext::tt::macro_parser;
use parse::lexer::comments::{doc_comment_style, strip_doc_comment_decoration};
use parse::lexer;
use parse;
use parse::token::{self, Token, Lit, intern_and_get_ident, InternedString};
use parse::token::Lit as PLit;
use std::rc::Rc;

/// # Token Trees
///
/// TokenTrees are syntactic forms for dealing with tokens. The description below is
/// more complete; in short a TokenTree is a single token, a delimited sequence of token
/// trees, or a sequence with repetition for list splicing as part of macro expansion.

/// A delimited sequence of token trees
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub struct Delimited {
    /// The type of delimiter
    pub delim: token::DelimToken,
    /// The span covering the opening delimiter
    pub open_span: Span,
    /// The delimited sequence of token trees
    pub tts: Vec<TokenTree>,
    /// The span covering the closing delimiter
    pub close_span: Span,
}

impl Delimited {
    /// Returns the opening delimiter as a token.
    pub fn open_token(&self) -> token::Token {
        token::OpenDelim(self.delim)
    }

    /// Returns the closing delimiter as a token.
    pub fn close_token(&self) -> token::Token {
        token::CloseDelim(self.delim)
    }

    /// Returns the opening delimiter as a token tree.
    pub fn open_tt(&self) -> TokenTree {
        TokenTree::Token(self.open_span, self.open_token())
    }

    /// Returns the closing delimiter as a token tree.
    pub fn close_tt(&self) -> TokenTree {
        TokenTree::Token(self.close_span, self.close_token())
    }
}

/// A sequence of token trees
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub struct SequenceRepetition {
    /// The sequence of token trees
    pub tts: Vec<TokenTree>,
    /// The optional separator
    pub separator: Option<token::Token>,
    /// Whether the sequence can be repeated zero (*), or one or more times (+)
    pub op: KleeneOp,
    /// The number of `MatchNt`s that appear in the sequence (and subsequences)
    pub num_captures: usize,
}

/// A Kleene-style [repetition operator](http://en.wikipedia.org/wiki/Kleene_star)
/// for token sequences.
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug, Copy)]
pub enum KleeneOp {
    ZeroOrMore,
    OneOrMore,
}

/// When the main rust parser encounters a syntax-extension invocation, it
/// parses the arguments to the invocation as a token-tree. This is a very
/// loose structure, such that all sorts of different AST-fragments can
/// be passed to syntax extensions using a uniform type.
///
/// If the syntax extension is an MBE macro, it will attempt to match its
/// LHS token tree against the provided token tree, and if it finds a
/// match, will transcribe the RHS token tree, splicing in any captured
/// macro_parser::matched_nonterminals into the `SubstNt`s it finds.
///
/// The RHS of an MBE macro is the only place `SubstNt`s are substituted.
/// Nothing special happens to misnamed or misplaced `SubstNt`s.
#[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
pub enum TokenTree {
    /// A single token
    Token(Span, token::Token),
    /// A delimited sequence of token trees
    Delimited(Span, Rc<Delimited>),

    // This only makes sense in MBE macros.

    /// A kleene-style repetition sequence with a span
    // FIXME(eddyb) #12938 Use DST.
    Sequence(Span, Rc<SequenceRepetition>),
}

impl TokenTree {
    pub fn len(&self) -> usize {
        match *self {
            TokenTree::Token(_, token::DocComment(name)) => {
                match doc_comment_style(&name.as_str()) {
                    AttrStyle::Outer => 2,
                    AttrStyle::Inner => 3
                }
            }
            TokenTree::Token(_, token::SpecialVarNt(..)) => 2,
            TokenTree::Token(_, token::MatchNt(..)) => 3,
            TokenTree::Delimited(_, ref delimed) => {
                delimed.tts.len() + 2
            }
            TokenTree::Sequence(_, ref seq) => {
                seq.tts.len()
            }
            TokenTree::Token(..) => 0
        }
    }

    pub fn get_tt(&self, index: usize) -> TokenTree {
        match (self, index) {
            (&TokenTree::Token(sp, token::DocComment(_)), 0) => {
                TokenTree::Token(sp, token::Pound)
            }
            (&TokenTree::Token(sp, token::DocComment(name)), 1)
            if doc_comment_style(&name.as_str()) == AttrStyle::Inner => {
                TokenTree::Token(sp, token::Not)
            }
            (&TokenTree::Token(sp, token::DocComment(name)), _) => {
                let stripped = strip_doc_comment_decoration(&name.as_str());

                // Searches for the occurrences of `"#*` and returns the minimum number of `#`s
                // required to wrap the text.
                let num_of_hashes = stripped.chars().scan(0, |cnt, x| {
                    *cnt = if x == '"' {
                        1
                    } else if *cnt != 0 && x == '#' {
                        *cnt + 1
                    } else {
                        0
                    };
                    Some(*cnt)
                }).max().unwrap_or(0);

                TokenTree::Delimited(sp, Rc::new(Delimited {
                    delim: token::Bracket,
                    open_span: sp,
                    tts: vec![TokenTree::Token(sp, token::Ident(token::str_to_ident("doc"))),
                              TokenTree::Token(sp, token::Eq),
                              TokenTree::Token(sp, token::Literal(
                                  token::StrRaw(token::intern(&stripped), num_of_hashes), None))],
                    close_span: sp,
                }))
            }
            (&TokenTree::Delimited(_, ref delimed), _) => {
                if index == 0 {
                    return delimed.open_tt();
                }
                if index == delimed.tts.len() + 1 {
                    return delimed.close_tt();
                }
                delimed.tts[index - 1].clone()
            }
            (&TokenTree::Token(sp, token::SpecialVarNt(var)), _) => {
                let v = [TokenTree::Token(sp, token::Dollar),
                         TokenTree::Token(sp, token::Ident(token::str_to_ident(var.as_str())))];
                v[index].clone()
            }
            (&TokenTree::Token(sp, token::MatchNt(name, kind)), _) => {
                let v = [TokenTree::Token(sp, token::SubstNt(name)),
                         TokenTree::Token(sp, token::Colon),
                         TokenTree::Token(sp, token::Ident(kind))];
                v[index].clone()
            }
            (&TokenTree::Sequence(_, ref seq), _) => {
                seq.tts[index].clone()
            }
            _ => panic!("Cannot expand a token tree")
        }
    }

    /// Returns the `Span` corresponding to this token tree.
    pub fn get_span(&self) -> Span {
        match *self {
            TokenTree::Token(span, _)     => span,
            TokenTree::Delimited(span, _) => span,
            TokenTree::Sequence(span, _)  => span,
        }
    }

    /// Use this token tree as a matcher to parse given tts.
    pub fn parse(cx: &base::ExtCtxt, mtch: &[TokenTree], tts: &[TokenTree])
                 -> macro_parser::NamedParseResult {
        // `None` is because we're not interpolating
        let arg_rdr = lexer::new_tt_reader_with_doc_flag(&cx.parse_sess().span_diagnostic,
                                                         None,
                                                         None,
                                                         tts.iter().cloned().collect(),
                                                         true);
        macro_parser::parse(cx.parse_sess(), cx.cfg(), arg_rdr, mtch)
    }
}

/// #Token Streams
///
/// TokenStreams are a syntactic abstraction over TokenTrees. The goal is for procedural
/// macros to work over TokenStreams instead of arbitrary syntax. For now, however, we
/// are going to cut a few corners (i.e., use some of the AST structure) when we need to
/// for backwards compatibility.

// TODO: A lot of the code in `libsyntax/ext` should be rewritable using TokenStreams.

/// TokenStreams are collections of TokenTrees that represent a syntactic structure. The 
/// struct itself shouldn't be directly manipulated; the internal structure is not stable,
/// and may be changed at any time in the future. The operators will not, however (except
/// for signatures, later on).
// #[derive(Clone, PartialEq, Eq, RustcEncodable, RustcDecodable, Hash, Debug)]
// pub struct TokenStream 
//   { trees : Vec<TokenTree>
//   , span  : Span
//   }

pub type TokenStream = Spanned<Vec<TokenTree>>;

pub fn compute_trees_span(trees : &[TokenTree]) -> Span {
  if trees.len() < 1 { return codemap::DUMMY_SP; }

  let mut lo_span;
  let mut hi_span;
  match trees[0]
    { TokenTree::Token(sp, _) | TokenTree::Delimited(sp, _) | TokenTree::Sequence(sp, _) => 
      { lo_span = sp.lo; hi_span = sp.hi; }
    }

  for tt in trees.iter().skip(1) {
    let loc_lo;
    let loc_hi;
    match *tt
      { TokenTree::Token(sp, _) | TokenTree::Delimited(sp, _) | TokenTree::Sequence(sp, _) => 
        { loc_lo = sp.lo; loc_hi = sp.hi; }
      }
    if loc_lo  < lo_span { lo_span = loc_lo; }
    if hi_span < loc_hi  { hi_span = loc_hi; }
  }

  codemap::mk_sp(lo_span, hi_span)
}

/// Convert a vector of `TokenTree`s into a `TokenStream`.
#[inline(always)]
pub fn tts_to_ts (trees : Vec<TokenTree>) -> TokenStream {
  let span = compute_trees_span(&trees);
  Spanned { node : trees, span : span }
}

pub fn ts_to_tts(stream : TokenStream) -> Vec<TokenTree> {
  stream.node.clone()
}

/// TokenStream operators include basic destructuring, boolean operations, `maybe_...`
/// operations, and `maybe_..._prefix` operations. Boolean operations are straightforward,
/// indicating information about the structure of the stream. The `maybe_...` operations
/// return `Some<...>` if the tokenstream contains the appropriate item. 
///
/// Similarly, the `maybe_..._prefix` operations potentially return a
/// partially-destructured stream as a pair where the first element is the expected item
/// and the second is the remainder of the stream. As anb example,
///
///    `maybe_path_prefix("a::b::c(a,b,c).foo()") -> (a::b::c, "(a,b,c).foo()")`
impl TokenStream {

  pub fn from_ast_lit_str(lit : ast::Lit) -> TokenStream {
    match lit.node
    { LitKind::Str(val, _) => {
        let val = PLit::Str_(token::intern(&val[..]));
        tts_to_ts(vec![TokenTree::Token(lit.span, Token::Literal(val, None))])
      }
      _ => panic!("Invalid literal '{:?}', expected string", lit)  
    }
    
  }

  pub fn from_interned_string_as_ident(s : InternedString) -> TokenStream {
    tts_to_ts(vec![TokenTree::Token(DUMMY_SP,Token::Ident(token::str_to_ident(&s[..])))])
  }

  pub fn to_trees(&self) -> Vec<TokenTree> { self.node.clone() }

  /// Returns with the first tree of the stream (if one exists)
  pub fn first_tree(&self) -> Option<TokenTree> {
    if (*self).node.len() > 1 { Some((*self).node[0].clone()) } else { None }
  }

  /// Drops the first tree of the stream
  pub fn drop_first_tree(&self) -> Option<TokenStream> {
    if (*self).node.len() < 1 { return None; }

    let mut local_trees = (*self).node.clone();
    let tts             = local_trees.split_off(1);

    Some(tts_to_ts(tts))
  }

  /// If the underlying stream has at least two elements, you'll get back the head and
  /// tail as new `TokenStream`s.
  pub fn unwind_cons(&self)     -> (Option<(TokenStream, TokenStream)>) {
    if (*self).node.len() < 1 { return None; }

    let mut tts = (*self).node.clone();
    let rst_tts = tts.split_off(1);
    let fst     = tts[0].clone();

    Some((tts_to_ts(vec![fst]), tts_to_ts(rst_tts)))
  }

  /// Indicates whether the `TokenStream` is empty.
  pub fn is_empty(&self) -> bool { self.node.len() == 0 }

  /// Indicates where the stream is of the form `= <ts>`, where `<ts>` is a continued
  /// `TokenStream`.
  pub fn is_assignment(&self) -> bool {
    if !((*self).node.len() > 1) { return false; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Token(_, Token::Eq) => true
      , _                              => false
      }
  }

  /// Indicatees where the stream is a single, delimited expression (e.g., `(a,b,c)` or
  /// `{a,b,c}`).
  pub fn is_delimited(&self) -> bool {
    if !((*self).node.len() == 1) { return false; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Delimited(_, _) => true
      , _                          => false
      }
  }
 
  /// Indicates if the stream is exactly one literal
  pub fn is_lit(&self) -> bool {
    if !((*self).node.len() == 1) { return false; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Token(_, Token::Literal(_,_)) => true
      , _                                  => false
      }
  }
  
  /// Indicates if the stream is exactly one identifier
  pub fn is_ident(&self) -> bool {
    if !((*self).node.len() == 1) { return false; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Token(_, Token::Ident(_)) => true
      , _                                    => false
      }
  }

  /// Returns the RHS of an assigment.
  pub fn maybe_assignment(&self) -> Option<TokenStream> {
    if !(self.is_assignment()) { return None; }
    
    self.drop_first_tree()
  }

  /// Returns the inside of the delimited term as a new TokenStream.
  pub fn maybe_delimited(&self) -> Option<TokenStream> {
    if !((*self).node.len() == 1) { return None; }

    match (*self).node[0]
      { TokenTree::Delimited(_, ref rc) => {
          let trees : Vec<TokenTree> = (*rc).tts.clone();
          Some(tts_to_ts(trees))
        }
      , _                               => None
      }
  }

  /// Returns a list of `TokenStream`s if the stream is a delimited list, breaking the
  /// stream on commas.
  pub fn maybe_comma_list(&self) -> Option<Vec<TokenStream>> {
    let maybe_tts = self.maybe_delimited();

    let mut ts : Vec<TokenTree>;
    match maybe_tts
      { Some(t) => { ts = t.node.clone(); }
      , None    => { return None; }
      }

    ts.reverse();
    let mut res        : Vec<TokenStream> = Vec::new();
    let mut current_ts : Vec<TokenTree>   = Vec::new();

    while ts.len() > 0 {
      let fst_tt = ts.pop();
      match fst_tt
        { Some(TokenTree::Token(_, Token::Comma)) => {
            res.push(tts_to_ts(current_ts));
            current_ts = Vec::new();
          }
        , Some(t) => { current_ts.push(t); }
        , None    => {} // How did we get here?
        }
    }
    res.push(tts_to_ts(current_ts));

    Some(res)
  }

  /// Convert a tokenstream to a metaitem
  pub fn maybe_metaitem(&self) -> Option<ast::MetaItem> {
    let sp = (*self).span;
    if let Some((id, ts)) = (*self).maybe_ident_prefix() {
      let name = intern_and_get_ident(&id.name.as_str()[..]);
      Some(Spanned { node : MetaItemKind { name : name
                                         , stream : ts }
                   , span : sp })
    } else { None }
  }

  /// Returns an identifier
  pub fn maybe_ident(&self) -> Option<ast::Ident> {
    if !((*self).node.len() == 1) { return None; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Token(_, Token::Ident(t)) => Some(t)
      , _                                    => None
      }
  }

  /// Returns a literal
  pub fn maybe_lit(&self) -> Option<token::Lit> {
    if !((*self).node.len() == 1) { return None; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Token(_, Token::Literal(l,_)) => Some(l)
      , _                                        => None
      }
  }

  /// Returns a string literal
  pub fn maybe_str_ast_lit(&self) -> Option<ast::Lit> {
    if !((*self).node.len() == 1) { return None; }

    let tt = (*self).node[0].clone();
    match tt
      { TokenTree::Token(_, Token::Literal(Lit::Str_(s),_)) => {
          let l = LitKind::Str(token::intern_and_get_ident(&parse::str_lit(&s.as_str())),
                               ast::StrStyle::Cooked);
          Some(Spanned { node : l , span : (*self).span})
        }
        _ => None
      }
  }

  /// Returns an identifier prefix
  pub fn maybe_ident_prefix(&self) -> Option<(ast::Ident, TokenStream)> {
    if let Some((t1, t2)) = self.unwind_cons() {
      if let Some(id) = t1.maybe_ident() {
        Some((id, t2))
      } else {
        None
      } 
    } else {
      None
    }
  }

  /// Returns a literal prefix
  pub fn maybe_lit_prefix(&self) -> Option<(token::Lit, TokenStream)> {
    if let Some((t1, t2)) = self.unwind_cons() {
      if let Some(id) = t1.maybe_lit() {
        Some((id, t2))
      } else {
        None
      } 
    } else {
      None
    }
  }

  /// Returns a non-global path prefix
  pub fn maybe_path_prefix(&self) -> Option<(ast::Path, TokenStream)> {
    let mut tts = (*self).node.clone();
    tts.reverse();
    let mut segments : Vec<ast::PathSegment> = Vec::new();
    let lo_span;
    let mut hi_span;

    let fst_id = tts.pop();

    match fst_id
      { Some(TokenTree::Token(span, Token::Ident(id))) => {
          lo_span = span.lo;
          hi_span = span.hi;
          segments.push(ast::PathSegment {
                          identifier : id,
                          parameters : ast::PathParameters::none(),
                       });
        }
      , _ => { return None; }
      }

    // Let's use a state machine to parse out the rest.
    let mut state = 0;
    let ans;

    loop {
      match state
        { 0 => { // State 0: Move to state 1 if we find a `::`, state 2 otherwise
           match tts.pop()
            { Some(TokenTree::Token(_, Token::ModSep)) => { state = 1; }
            , Some(t)                                  => { tts.push(t); state = 2; }
            , None                                     => { state = 2;  }
            }
          }
        , 1 => { // State 1: Move to state 0 if we can an ident, state 3 otherwise
            match tts.pop()
              { Some(TokenTree::Token(span, Token::Ident(id))) => {
                  hi_span = span.hi;
                  segments.push(ast::PathSegment
                                 { identifier : id
                                 , parameters : ast::PathParameters::none()
                                 }
                               );
                  state = 0;
                }
              , _ => { state = 3; }
              }
           }
       , 2 => { // State 2: Finish up
           let path = ast::Path{ span : mk_sp(lo_span,hi_span)
                               , global : false
                               , segments : segments
                               };
           tts.reverse();
           let new_ts = tts_to_ts(tts);
           ans = Some((path,new_ts));
           break;
         }
      ,  _ => { ans = None; break; } // State 3+: Fail
      }
    }

    ans
  }

}

#[cfg(test)]
mod tests {
  use super::*;
  use ast;
  // use codemap::{Span, BytePos, Pos, Spanned, NO_EXPANSION};
  use codemap::{Span, BytePos, NO_EXPANSION};
  use parse::token::{self, str_to_ident, Token, Lit};
  use util::parser_testing::{string_to_tts};
  use std::rc::Rc;

  // produce a codemap::span
  fn sp(a: u32, b: u32) -> Span {
    Span {lo: BytePos(a), hi: BytePos(b), expn_id: NO_EXPANSION}
  }

  #[test]
  fn test_is_empty() {
    let test0 = tts_to_ts(Vec::new());
    let test1 = tts_to_ts(vec![TokenTree::Token(sp(0,1),Token::Ident(str_to_ident("a")))]);
    let test2 = tts_to_ts(string_to_tts("foo(bar::baz)".to_string()));

    assert_eq!(test0.is_empty(), true);
    assert_eq!(test1.is_empty(), false);
    assert_eq!(test2.is_empty(), false);
  }

  #[test]
  fn test_is_delimited() {
    let test0 = tts_to_ts(string_to_tts("foo(bar::baz)".to_string()));
    let test1 = tts_to_ts(string_to_tts("(bar::baz)".to_string()));
    let test2 = tts_to_ts(string_to_tts("(foo,bar,baz)".to_string()));
    let test3 = tts_to_ts(string_to_tts("(foo,bar,baz)(zab,rab,oof)".to_string()));
    let test4 = tts_to_ts(string_to_tts("(foo,bar,baz)foo".to_string()));
    let test5 = tts_to_ts(string_to_tts("".to_string()));

    assert_eq!(test0.is_delimited(), false);
    assert_eq!(test1.is_delimited(), true);
    assert_eq!(test2.is_delimited(), true);
    assert_eq!(test3.is_delimited(), false);
    assert_eq!(test4.is_delimited(), false);
    assert_eq!(test5.is_delimited(), false);
  }

  #[test]
  fn test_is_assign() {
    let test0 = tts_to_ts(string_to_tts("= bar::baz".to_string()));
    let test1 = tts_to_ts(string_to_tts("= \"5\"".to_string()));
    let test2 = tts_to_ts(string_to_tts("= 5".to_string()));
    let test3 = tts_to_ts(string_to_tts("(foo = 10)".to_string()));
    let test4 = tts_to_ts(string_to_tts("= (foo,bar,baz)".to_string()));
    let test5 = tts_to_ts(string_to_tts("".to_string()));

    assert_eq!(test0.is_assignment(), true);
    assert_eq!(test1.is_assignment(), true);
    assert_eq!(test2.is_assignment(), true);
    assert_eq!(test3.is_assignment(), false);
    assert_eq!(test4.is_assignment(), true);
    assert_eq!(test5.is_assignment(), false);
  }

  #[test]
  fn test_is_lit() {
    let test0 = tts_to_ts(string_to_tts("\"foo\"".to_string()));
    let test1 = tts_to_ts(string_to_tts("5".to_string()));
    let test2 = tts_to_ts(string_to_tts("foo".to_string()));
    let test3 = tts_to_ts(string_to_tts("foo::bar".to_string()));
    let test4 = tts_to_ts(string_to_tts("foo(bar)".to_string()));

    assert_eq!(test0.is_lit(), true);
    assert_eq!(test1.is_lit(), true);
    assert_eq!(test2.is_lit(), false);
    assert_eq!(test3.is_lit(), false);
    assert_eq!(test4.is_lit(), false);
  }

  #[test]
  fn test_is_ident() {
    let test0 = tts_to_ts(string_to_tts("\"foo\"".to_string()));
    let test1 = tts_to_ts(string_to_tts("5".to_string()));
    let test2 = tts_to_ts(string_to_tts("foo".to_string()));
    let test3 = tts_to_ts(string_to_tts("foo::bar".to_string()));
    let test4 = tts_to_ts(string_to_tts("foo(bar)".to_string()));
    
    assert_eq!(test0.is_ident(), false);
    assert_eq!(test1.is_ident(), false);
    assert_eq!(test2.is_ident(), true);
    assert_eq!(test3.is_ident(), false);
    assert_eq!(test4.is_ident(), false);
  }


  #[test]
  fn test_maybe_assignment() { 
    let test0 = tts_to_ts(string_to_tts("= bar::baz".to_string())).maybe_assignment();
    let test1 = tts_to_ts(string_to_tts("= \"5\"".to_string())).maybe_assignment();
    let test2 = tts_to_ts(string_to_tts("= 5".to_string())).maybe_assignment();
    let test3 = tts_to_ts(string_to_tts("(foo = 10)".to_string())).maybe_assignment();
    let test4 = tts_to_ts(string_to_tts("= (foo,bar,baz)".to_string())).maybe_assignment();
    let test5 = tts_to_ts(string_to_tts("".to_string())).maybe_assignment();

    let test0_expected = tts_to_ts(vec![ TokenTree::Token(sp(2,5), token::Ident(str_to_ident("bar")))
                                       , TokenTree::Token(sp(5,7), token::ModSep)
                                       , TokenTree::Token(sp(7,10),token::Ident(str_to_ident("baz")))
                                       ]);
    assert_eq!(test0, Some(test0_expected));

    let test1_expected = 
      tts_to_ts(vec![TokenTree::Token( sp(2,5),token::Literal(Lit::Str_( token::intern("5")) 
                                                                       , None))]);
    assert_eq!(test1,Some(test1_expected));
    
    let test2_expected = tts_to_ts(vec![TokenTree::Token( sp(2,3)
                                       , token::Literal(
                                           Lit::Integer( 
                                             token::intern(&(5.to_string()))),
                                             None))]);
    assert_eq!(test2,Some(test2_expected));
    
    assert_eq!(test3,None);

    let test4_expected =
      tts_to_ts(
        vec![
          TokenTree::Delimited( 
              sp(2,15)
            , Rc::new(Delimited 
                        { delim     : token::DelimToken::Paren
                        , open_span : sp(2,3)
                        , tts       : vec![ TokenTree::Token(sp( 3, 6), 
                                                             token::Ident(str_to_ident("foo")))
                                          , TokenTree::Token(sp( 6, 7), 
                                                             token::Comma)
                                          , TokenTree::Token(sp( 7,10), 
                                                             token::Ident(str_to_ident("bar")))
                                          , TokenTree::Token(sp(10,11), 
                                                             token::Comma)
                                          , TokenTree::Token(sp(11,14), 
                                                             token::Ident(str_to_ident("baz")))
                                          ]
                        , close_span : sp(14,15)
                        }))]);
    assert_eq!(test4,Some(test4_expected));
    
    assert_eq!(test5,None);
    
  }

  #[test]
  fn test_maybe_delimited() {
    let test0 = tts_to_ts(string_to_tts("foo(bar::baz)".to_string())).maybe_delimited();
    let test1 = tts_to_ts(string_to_tts("(bar::baz)".to_string())).maybe_delimited();
    let test2 = tts_to_ts(string_to_tts("(foo,bar,baz)".to_string())).maybe_delimited();
    let test3 = tts_to_ts(string_to_tts("(foo,bar,baz)(zab,rab)".to_string())).maybe_delimited();
    let test4 = tts_to_ts(string_to_tts("(foo,bar,baz)foo".to_string())).maybe_delimited();
    let test5 = tts_to_ts(string_to_tts("".to_string())).maybe_delimited();

    assert_eq!(test0, None);

    let test1_expected = 
      tts_to_ts(vec![ TokenTree::Token(sp(1,4), token::Ident(str_to_ident("bar")))
                    , TokenTree::Token(sp(4,6), token::ModSep)
                    , TokenTree::Token(sp(6,9), token::Ident(str_to_ident("baz")))
                    ]); 
    assert_eq!(test1, Some(test1_expected));

    let test2_expected = 
      tts_to_ts(vec![ TokenTree::Token(sp(1, 4), token::Ident(str_to_ident("foo")))
                    , TokenTree::Token(sp(4, 5), token::Comma)
                    , TokenTree::Token(sp(5, 8), token::Ident(str_to_ident("bar")))
                    , TokenTree::Token(sp(8, 9), token::Comma)
                    , TokenTree::Token(sp(9,12), token::Ident(str_to_ident("baz")))
                    ]); 
    assert_eq!(test2, Some(test2_expected));

    assert_eq!(test3, None);
 
    assert_eq!(test4, None);

    assert_eq!(test5, None);
  }

  #[test]
  fn test_maybe_comma_list() {
    let test0 = tts_to_ts(string_to_tts("foo(bar::baz)".to_string())).maybe_comma_list();
    let test1 = tts_to_ts(string_to_tts("(bar::baz)".to_string())).maybe_comma_list();
    let test2 = tts_to_ts(string_to_tts("(foo,bar,baz)".to_string())).maybe_comma_list();
    let test3 = tts_to_ts(string_to_tts("(foo::bar,bar,baz)".to_string())).maybe_comma_list();
    let test4 = tts_to_ts(string_to_tts("(foo,bar,baz)(zab,rab)".to_string())).maybe_comma_list();
    let test5 = tts_to_ts(string_to_tts("(foo,bar,baz)foo".to_string())).maybe_comma_list();
    let test6 = tts_to_ts(string_to_tts("".to_string())).maybe_comma_list();

    assert_eq!(test0, None);

    let test1_expected : Vec<TokenStream> = 
      vec![tts_to_ts(vec![ TokenTree::Token(sp(1,4), token::Ident(str_to_ident("bar")))
                         , TokenTree::Token(sp(4,6), token::ModSep)
                         , TokenTree::Token(sp(6,9), token::Ident(str_to_ident("baz")))
                         ])]; 
    assert_eq!(test1, Some(test1_expected));

    let test2_expected : Vec<TokenStream> =
      vec![ tts_to_ts(vec![TokenTree::Token(sp(1, 4), token::Ident(str_to_ident("foo")))])
          , tts_to_ts(vec![TokenTree::Token(sp(5, 8), token::Ident(str_to_ident("bar")))]) 
          , tts_to_ts(vec![TokenTree::Token(sp(9,12), token::Ident(str_to_ident("baz")))]) 
          ];
    assert_eq!(test2, Some(test2_expected));

    let test3_expected : Vec<TokenStream> = 
      vec![ tts_to_ts(vec![ TokenTree::Token(sp(1,4), token::Ident(str_to_ident("foo")))
                          , TokenTree::Token(sp(4,6), token::ModSep)
                          , TokenTree::Token(sp(6,9), token::Ident(str_to_ident("bar")))
                          ])
          , tts_to_ts(vec![TokenTree::Token(sp(10,13), token::Ident(str_to_ident("bar")))])
          , tts_to_ts(vec![TokenTree::Token(sp(14,17), token::Ident(str_to_ident("baz")))])
          ]; 
    assert_eq!(test3, Some(test3_expected));
 
    assert_eq!(test4, None);

    assert_eq!(test5, None);

    assert_eq!(test6, None);
  }

 #[test]
  fn test_maybe_ident() {
    let test0 = tts_to_ts(string_to_tts("\"foo\"".to_string())).maybe_ident();
    let test1 = tts_to_ts(string_to_tts("5".to_string())).maybe_ident();
    let test2 = tts_to_ts(string_to_tts("foo".to_string())).maybe_ident();
    let test3 = tts_to_ts(string_to_tts("foo::bar".to_string())).maybe_ident();
    let test4 = tts_to_ts(string_to_tts("foo(bar)".to_string())).maybe_ident();
    
    assert_eq!(test0, None);
    assert_eq!(test1, None);
    assert_eq!(test2, Some(str_to_ident("foo")));
    assert_eq!(test3, None);
    assert_eq!(test4, None);
  }

  #[test]
  fn test_maybe_lit() {
    let test0 = tts_to_ts(string_to_tts("\"foo\"".to_string())).maybe_lit();
    let test1 = tts_to_ts(string_to_tts("5".to_string())).maybe_lit();
    let test2 = tts_to_ts(string_to_tts("foo".to_string())).maybe_lit();
    let test3 = tts_to_ts(string_to_tts("foo::bar".to_string())).maybe_lit();
    let test4 = tts_to_ts(string_to_tts("foo(bar)".to_string())).maybe_lit();

    assert_eq!(test0, Some(Lit::Str_( token::intern("foo"))));
    assert_eq!(test1, Some(Lit::Integer(token::intern(&(5.to_string())))));
    assert_eq!(test2, None);
    assert_eq!(test3, None);
    assert_eq!(test4, None);
  }

  #[test]
  fn test_maybe_path_prefix() {
    let test0 = tts_to_ts(string_to_tts("foo(bar::baz)".to_string())).maybe_path_prefix();
    let test1 = tts_to_ts(string_to_tts("(bar::baz)".to_string())).maybe_path_prefix();
    let test2 = tts_to_ts(string_to_tts("(foo,bar,baz)".to_string())).maybe_path_prefix();
    let test3 = tts_to_ts(string_to_tts("foo::bar(bar,baz)".to_string())).maybe_path_prefix();

    
    let test0_expected = Some((ast::Path::from_ident(sp(0,3), str_to_ident("foo")),
                              tts_to_ts(vec![TokenTree::Delimited(
                                              sp(3,13),
                                              Rc::new(Delimited 
                                                       { delim : token::DelimToken::Paren
                                                       , open_span : sp(3,4)
                                                       , tts : vec!
                                                           [ TokenTree::Token(sp(4,7), 
                                                                              token::Ident(str_to_ident("bar")))
                                                           , TokenTree::Token(sp(7,9), token::ModSep)
                                                           , TokenTree::Token(sp(9,12), 
                                                                              token::Ident(str_to_ident("baz")))
                                                           ]
                                                       , close_span : sp(12,13)
                                              }))])));
    assert_eq!(test0, test0_expected);

    assert_eq!(test1, None);
    assert_eq!(test2, None);

    let test3_path = ast::Path 
      { span: sp(0,8)
      , global: false
      , segments: vec!
                    [ ast::PathSegment 
                        { identifier : str_to_ident("foo")
                        , parameters : ast::PathParameters::none()
                        }
                    , ast::PathSegment 
                        { identifier : str_to_ident("bar")
                        , parameters : ast::PathParameters::none()
                        }
                    ]
      };

    let test3_stream = tts_to_ts(vec![TokenTree::Delimited(
                                          sp(8,17),
                                          Rc::new(Delimited 
                                                   { delim : token::DelimToken::Paren
                                                   , open_span : sp(8,9)
                                                   , tts : vec!
                                                       [ TokenTree::Token(sp(9,12), 
                                                                          token::Ident(str_to_ident("bar")))
                                                       , TokenTree::Token(sp(12,13), token::Comma)
                                                       , TokenTree::Token(sp(13,16), 
                                                                          token::Ident(str_to_ident("baz")))
                                                       ]
                                                   , close_span : sp(16,17)
                                          }))]);
    let test3_expected = Some((test3_path, test3_stream));
    assert_eq!(test3, test3_expected);
  } 

  #[test]
  fn test_maybe_lit_prefix() {
    let test0 = tts_to_ts(string_to_tts("\"foo\" bar".to_string())).maybe_lit_prefix();
    let test1 = tts_to_ts(string_to_tts("5".to_string())).maybe_lit_prefix();
    let test2 = tts_to_ts(string_to_tts("foo".to_string())).maybe_lit_prefix();
    let test3 = tts_to_ts(string_to_tts("foo::bar".to_string())).maybe_lit_prefix();
    let test4 = tts_to_ts(string_to_tts("foo(bar)".to_string())).maybe_lit_prefix();

    assert_eq!(test0, Some((Lit::Str_( token::intern("foo")), 
                           tts_to_ts(vec![TokenTree::Token(sp(6,9),
                                          token::Ident(str_to_ident("bar")))]))));
    assert_eq!(test1, Some((Lit::Integer(token::intern(&(5.to_string()))),
                            tts_to_ts(vec![]))));
    assert_eq!(test2, None);
    assert_eq!(test3, None);
    assert_eq!(test4, None);
  }

  #[test]
  fn test_maybe_ident_prefix() {
    let test0 = tts_to_ts(string_to_tts("\"foo\" bar".to_string())).maybe_ident_prefix();
    let test1 = tts_to_ts(string_to_tts("5".to_string())).maybe_ident_prefix();
    let test2 = tts_to_ts(string_to_tts("foo".to_string())).maybe_ident_prefix();
    let test3 = tts_to_ts(string_to_tts("foo::bar".to_string())).maybe_ident_prefix();
    let test4 = tts_to_ts(string_to_tts("foo(bar)".to_string())).maybe_ident_prefix();

    assert_eq!(test0, None);
    assert_eq!(test1, None);
    assert_eq!(test2, Some((str_to_ident("foo"), tts_to_ts(vec![]))));


    let test3_stream = tts_to_ts(vec![TokenTree::Token(sp(3,5), token::ModSep)
															       ,TokenTree::Token(sp(5,8), token::Ident(str_to_ident("bar")))]);
    assert_eq!(test3, Some((str_to_ident("foo"), test3_stream)));

		let test4_stream = tts_to_ts(vec![TokenTree::Delimited(
                                          sp(3,8),
                                          Rc::new(Delimited 
                                                   { delim : token::DelimToken::Paren
                                                   , open_span : sp(3,4)
                                                   , tts : vec!
                                                       [ TokenTree::Token(sp(4,7), 
                                                                          token::Ident(str_to_ident("bar")))
                                                       ]
                                                   , close_span : sp(7,8)
                                          }))]);

    assert_eq!(test4, Some((str_to_ident("foo"), test4_stream)));
  }

}

