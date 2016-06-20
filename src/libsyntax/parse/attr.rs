// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use attr;
use ast::{self, Path};
use codemap::{spanned, Spanned, mk_sp, Span};
use parse::common::SeqSep;
use parse::PResult;
use parse::token::{self, str_to_ident};
use parse::parser::{Parser, TokenType, PathStyle};
use ptr::P;
use tokenstream::{self, TokenTree};

impl<'a> Parser<'a> {
    /// Parse attributes that appear before an item
    pub fn parse_outer_attributes(&mut self) -> PResult<'a, Vec<ast::Attribute>> {
        let mut attrs: Vec<ast::Attribute> = Vec::new();
        loop {
            debug!("parse_outer_attributes: self.token={:?}", self.token);
            match self.token {
                token::Pound => {
                    attrs.push(self.parse_attribute(false)?);
                }
                token::DocComment(s) => {
                    debug!("Making doc comment!");
                    let name = self.id_to_interned_str(ast::Ident::with_empty_ctxt(s));
                    let attr = ::attr::mk_sugared_doc_attr(attr::mk_attr_id(), 
                                                           name,
                                                           self.span.lo,
                                                           self.span.hi);

                    if attr.node.style != ast::AttrStyle::Outer {
                        let mut err = self.fatal("expected outer doc comment");
                        err.note("inner doc comments like this (starting with \
                                  `//!` or `/*!`) can only appear before items");
                        return Err(err);
                    }
                    debug!("Doc comment: {:?}", attr);
                    attrs.push(attr);
                    self.bump();
                }
                _ => break,
            }
        }
        return Ok(attrs);
    }

    /// Matches `attribute = # ! [ meta_item ]`
    ///
    /// If permit_inner is true, then a leading `!` indicates an inner
    /// attribute
    pub fn parse_attribute(&mut self, permit_inner: bool) -> PResult<'a, ast::Attribute> {
        debug!("parse_attribute: permit_inner={:?} self.token={:?}",
               permit_inner,
               self.token);
        let (span, path, stream, mut style) = match self.token {
            token::Pound => {
                debug!("parse_attributes: self.token={:?}", self.token);
                let lo = self.span.lo;
                self.bump();

                if permit_inner {
                    debug!("parse_attributes: self.token={:?}", self.token);
                    self.expected_tokens.push(TokenType::Token(token::Not));
                }
                let style = if self.token == token::Not {
                    self.bump();
                    if !permit_inner {
                        let span = self.span;
                        self.diagnostic()
                            .struct_span_err(span,
                                             "an inner attribute is not permitted in this context")
                            .help("place inner attribute at the top of the module or \
                                   block")
                            .emit()
                    }
                    ast::AttrStyle::Inner
                } else {
                    ast::AttrStyle::Outer
                };

                debug!("parse_attributes: self.token={:?}", self.token);
                self.expect(&token::OpenDelim(token::Bracket))?;

                debug!("parse_attributes: self.token={:?}", self.token);
                let nt_meta = match self.token {
                    token::Interpolated(token::NtMeta(ref e)) => Some(e.clone()),
                    _ => None,
                };

                match nt_meta {
                    Some(meta) => {
                        self.bump(); // bump the metaitem
                        self.expect(&token::CloseDelim(token::Bracket))?;
                        debug!("Found metaitem, handing that back");
                        return Ok(Spanned { 
                                   span : meta.span,
                                   node : ast::Attribute_ {
                                     id : attr::mk_attr_id(),
                                     style: style,
                                     path: Path::from_ident(meta.span, str_to_ident(&meta.node.name[..])),
                                     stream: meta.node.stream.clone(),
                                     is_sugared_doc: false
                                    }});
                    }
                    None => {}
                }
 
                debug!("parse_attributes: self.token={:?}", self.token);
                let path = self.parse_path(PathStyle::Mod)?;
                debug!("parse_attributes: self.token={:?}", self.token);
                let mut tts : Vec<TokenTree> = Vec::new();
                loop {
                  match self.token {
                    token::CloseDelim(token::Bracket) => { 
                      break }
                    _ => {
                      let tt = self.parse_token_tree()?;
                      tts.push(tt);
                    }
                  }
                }
                debug!("parse_attributes: self.token={:?}", self.token);
                self.expect(&token::CloseDelim(token::Bracket))?;
                let hi = self.span.hi;

                (mk_sp(lo, hi), path, tokenstream::tts_to_ts(tts), style)
            }
            _ => {
                let token_str = self.this_token_to_string();
                return Err(self.fatal(&format!("expected `#`, found `{}`", token_str)));
            }
        };

        if permit_inner && self.token == token::Semi {
            self.bump();
            self.span_warn(span,
                           "this inner attribute syntax is deprecated. The new syntax is \
                            `#![foo]`, with a bang and no semicolon");
            style = ast::AttrStyle::Inner;
        }

        Ok(Spanned {
            span: span,
            node: ast::Attribute_ {
                id: attr::mk_attr_id(),
                style: style,
                path: path,
                stream: stream,
                is_sugared_doc: false,
            },
        })
    }

    /// Parse attributes that appear after the opening of an item. These should
    /// be preceded by an exclamation mark, but we accept and warn about one
    /// terminated by a semicolon.

    /// matches inner_attrs*
    pub fn parse_inner_attributes(&mut self) -> PResult<'a, Vec<ast::Attribute>> {
        let mut attrs: Vec<ast::Attribute> = vec![];
        loop {
            match self.token {
                token::Pound => {
                    // Don't even try to parse if it's not an inner attribute.
                    if !self.look_ahead(1, |t| t == &token::Not) {
                        break;
                    }

                    let attr = self.parse_attribute(true)?;
                    assert!(attr.node.style == ast::AttrStyle::Inner);
                    attrs.push(attr);
                }
                token::DocComment(s) => {
                    // we need to get the position of this token before we bump.
                    let Span { lo, hi, .. } = self.span;
                    let name = self.id_to_interned_str(ast::Ident::with_empty_ctxt(s));
                    let attr = attr::mk_sugared_doc_attr(attr::mk_attr_id(), name, lo, hi);
                    if attr.node.style == ast::AttrStyle::Inner {
                        attrs.push(attr);
                        self.bump();
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        Ok(attrs)
    }

    /// matches 
    /// meta_item = IDENT
    ///           | IDENT = <tt>
    ///           | IDENT <tt> (where <tt> is `(...)`)

    // TODO What to do here? I think the right thing is to just parse it like it's an
    // old-style meta_item and then induce the tokenstream structure at the end.
    pub fn parse_meta_item(&mut self) -> PResult<'a, P<ast::MetaItem>> {
      let nt_meta = match self.token {
          token::Interpolated(token::NtMeta(ref e)) => Some(e.clone()),
          _ => None,
      };

      match nt_meta {
          Some(meta) => {
              self.bump();
              return Ok(meta);
          }
          None => {}
      }

      let lo = self.span.lo;
      let ident = self.parse_ident()?;
      let name = self.id_to_interned_str(ident);

      let mut tts : Vec<TokenTree> = Vec::new();
      match self.token {
          token::Eq => {
            // grab up that equal sign
            let tt = self.parse_token_tree()?; 
            tts.push(tt);

            // and whatever is next (and let's hope there's only one thing)
            let tt = self.parse_token_tree()?;
            tts.push(tt);
          }
          token::OpenDelim(token::Paren) => {
            let tt = self.parse_token_tree()?; 
            tts.push(tt);
          }
          _ => { }
      }

      let hi = self.span.hi;
      Ok(P(spanned(lo, hi, ast::MetaItemKind
                             { name   : name
                             , stream : tokenstream::tts_to_ts(tts)
                             })))
    }

    /// matches meta_seq = ( COMMASEP(meta_item) )
    fn parse_meta_seq(&mut self) -> PResult<'a, Vec<P<ast::MetaItem>>> {
        self.parse_unspanned_seq(&token::OpenDelim(token::Paren),
                                 &token::CloseDelim(token::Paren),
                                 SeqSep::trailing_allowed(token::Comma),
                                 |p: &mut Parser<'a>| p.parse_meta_item())
    }
}
