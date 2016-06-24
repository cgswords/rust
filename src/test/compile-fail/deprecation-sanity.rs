// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Various checks that deprecation attributes are used correctly

mod bogus_attribute_types_1 {
    #[deprecated(since = "a", note = "a", reason)] //~ ERROR incorrect attribute item 'reason', expected items 'since', 'note'
    fn f1() { }

    #[deprecated(since = "a", note)] //~ ERROR incorrect attribute format for 'note', expected 'note = "value"'
    fn f2() { }

    #[deprecated(since, note = "a")] //~ ERROR incorrect attribute format for 'since', expected 'since = "value"'
    fn f3() { }

    #[deprecated(since = "a", note(b))] //~ ERROR incorrect attribute format for 'note', expected 'note = "value"'
    fn f5() { }

    #[deprecated(since(b), note = "a")] //~ ERROR incorrect attribute format for 'since', expected 'since = "value"'
    fn f6() { }
}

#[deprecated(since = "a", note = "b")]
#[deprecated(since = "a", note = "b")]
fn multiple1() { } //~ ERROR multiple deprecated attributes

#[deprecated(since = "a", since = "b", note = "c")] //~ ERROR multiple 'since' items
fn f1() { }

fn main() { }

