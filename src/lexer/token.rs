//! The [`Token`] type and associated definitions.

use std::{
    iter::Enumerate,
    ops::{Deref, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive},
    str::FromStr,
};

use nom::{error::VerboseError, Compare, InputIter, InputLength, InputTake, Needed, Slice};

use crate::{int::ImpSize, var::Var};

use super::parse_tokens;

/// A token generated by parsing valid IMP source code.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token<'src, T = ImpSize> {
    /// A single semicolon (`;`).
    Semicolon,
    /// A single left parenthesis (`(`).
    LeftParen,
    /// A single right parenthesis (`)`).
    RightParen,
    /// The `skip` keyword.
    Skip,
    /// The assignment operator (`:=`).
    Assign,
    /// A single asterisk (`*`).
    Star,
    /// A single plus sign (`+`).
    Plus,
    /// A single minus sign (`-`).
    Minus,
    /// The `if` keyword.
    If,
    /// The `then` keyword.
    Then,
    /// The `else` keyword.
    Else,
    /// The `fi` keyword.
    Fi,
    /// The `while` keyword.
    While,
    /// The `do` keyword.
    Do,
    /// The `od` keyword.
    Od,
    /// The `true` keyword.
    True,
    /// The `false` keyword.
    False,
    /// A single equals sign (`=`).
    Equals,
    /// A single left angle bracket (`<`).
    LeftAngleBracket,
    /// A single right angle bracket (`>`).
    RightAngleBracket,
    /// The `not` keyword.
    Not,
    /// The `and` keyword,
    And,
    /// The `or` keyword,
    Or,
    /// A variable name.
    Var(Var<'src>),
    /// An integer value.
    Int(T),
}

impl<'src, T> InputLength for Token<'src, T> {
    #[inline]
    fn input_len(&self) -> usize {
        1
    }
}

/// A thin wrapper around an owned [`Token`] slice,
/// from which [`TokensRef`] structs can be cheaply
/// created and passed around.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Tokens<'src, T = ImpSize> {
    /// The underlying [`Token`] buffer.
    tokens: Box<[Token<'src, T>]>,
}

impl<'src, T> Deref for Tokens<'src, T> {
    type Target = [Token<'src, T>];

    fn deref(&self) -> &Self::Target {
        self.tokens.as_ref()
    }
}

impl<'src, T: FromStr> TryFrom<&'src str> for Tokens<'src, T> {
    type Error = VerboseError<&'src str>;

    fn try_from(value: &'src str) -> Result<Self, Self::Error> {
        parse_tokens(value).map(|tokens| Self {
            tokens: tokens.into_boxed_slice(),
        })
    }
}

impl<'src, T> Tokens<'src, T> {
    /// Creates a new [`Tokens`] by cloning the given `tokens`.
    pub fn new(tokens: &[Token<'src, T>]) -> Self
    where
        T: Clone,
    {
        Self {
            tokens: tokens.to_vec().into_boxed_slice(),
        }
    }

    /// Returns a [`TokensRef`] pointing at the [`Token`] buffer owned by `self`.
    pub fn as_ref<'buf>(&'buf self) -> TokensRef<'buf, 'src, T> {
        self.tokens.as_ref().into()
    }

    /// Returns a reference to the underlying [`Token`] buffer as a slice.
    pub fn as_slice(&self) -> &[Token<'src, T>] {
        self.tokens.as_ref()
    }
}

/// A reference to a [`Tokens`], largely used as a newtype
/// for implementing various [`nom`] traits.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TokensRef<'buf, 'src, T = usize> {
    /// A reference to the underlying buffer of a [`Tokens`].
    tokens: &'buf [Token<'src, T>],
}

impl<'buf, 'src, T> Deref for TokensRef<'buf, 'src, T> {
    type Target = &'buf [Token<'src, T>];

    fn deref(&self) -> &Self::Target {
        &self.tokens
    }
}

impl<'buf, 'src, T> From<&'buf [Token<'src, T>]> for TokensRef<'buf, 'src, T> {
    fn from(value: &'buf [Token<'src, T>]) -> Self {
        Self { tokens: value }
    }
}

impl<'buf, 'src, T> From<&'buf Tokens<'src, T>> for TokensRef<'buf, 'src, T> {
    fn from(value: &'buf Tokens<'src, T>) -> Self {
        value.deref().into()
    }
}

impl<'buf, 'src, T: Eq> Compare<Token<'src, T>> for TokensRef<'buf, 'src, T> {
    fn compare(&self, t: Token<'src, T>) -> nom::CompareResult {
        match self.len() {
            0 => nom::CompareResult::Incomplete,
            _ if *self.first().unwrap() == t => nom::CompareResult::Ok,
            _ => nom::CompareResult::Error,
        }
    }

    fn compare_no_case(&self, t: Token<'src, T>) -> nom::CompareResult {
        self.compare(t)
    }
}

// the "l" and "r" suffixes are associated with the positions of the operands
// (left and right respectively)
impl<'bufl, 'bufr, 'srcl, 'srcr, T: Eq> Compare<TokensRef<'bufr, 'srcr, T>>
    for TokensRef<'bufl, 'srcl, T>
{
    #[inline]
    fn compare(&self, t: TokensRef<'bufr, 'srcr, T>) -> nom::CompareResult {
        // we look for the first index where self and t differ
        match self
            .iter()
            .zip(t.iter())
            .position(|(left, right)| left != right)
        {
            Some(_) => nom::CompareResult::Error,
            None if self.len() < t.len() => nom::CompareResult::Incomplete,
            None => nom::CompareResult::Ok,
        }
    }

    fn compare_no_case(&self, t: TokensRef<'bufr, 'srcr, T>) -> nom::CompareResult {
        // tokens have no concept of casing, so this just transparently invokes Compare::compare
        self.compare(t)
    }
}

impl<'buf, 'src, T> Slice<Range<usize>> for TokensRef<'buf, 'src, T> {
    fn slice(&self, range: Range<usize>) -> Self {
        Self::new(self.tokens.slice(range))
    }
}

impl<'buf, 'src, T> Slice<RangeFrom<usize>> for TokensRef<'buf, 'src, T> {
    fn slice(&self, range: RangeFrom<usize>) -> Self {
        Self::new(self.tokens.slice(range))
    }
}

impl<'buf, 'src, T> Slice<RangeTo<usize>> for TokensRef<'buf, 'src, T> {
    fn slice(&self, range: RangeTo<usize>) -> Self {
        Self::new(self.tokens.slice(range))
    }
}

impl<'buf, 'src, T> Slice<RangeFull> for TokensRef<'buf, 'src, T> {
    fn slice(&self, range: RangeFull) -> Self {
        Self::new(self.tokens.slice(range))
    }
}

impl<'buf, 'src, T> Slice<RangeInclusive<usize>> for TokensRef<'buf, 'src, T> {
    fn slice(&self, range: RangeInclusive<usize>) -> Self {
        self.slice(*range.start()..(range.end() + 1))
    }
}

impl<'buf, 'src, T> Slice<RangeToInclusive<usize>> for TokensRef<'buf, 'src, T> {
    fn slice(&self, range: RangeToInclusive<usize>) -> Self {
        self.slice(..(range.end + 1))
    }
}

impl<'buf, 'src, T> InputTake for TokensRef<'buf, 'src, T> {
    fn take(&self, count: usize) -> Self {
        Self::new(self.tokens.split_at(count).0)
    }

    fn take_split(&self, count: usize) -> (Self, Self) {
        let (tail, head) = self.tokens.split_at(count);
        // for presumably deranged reasons, nom expects this pair
        // to be in the reverse order as compared to the output
        // of std::slice::split_at. it's probably just to fit with
        // the "(tail, head)" idiom from the rest of nom, but i
        // still hate it
        (Self::new(head), Self::new(tail))
    }
}

impl<'buf, 'src, T> InputLength for TokensRef<'buf, 'src, T> {
    fn input_len(&self) -> usize {
        self.tokens.len()
    }
}

impl<'buf, 'src, T> InputIter for TokensRef<'buf, 'src, T> {
    type Item = &'buf Token<'src, T>;

    type Iter = Enumerate<std::slice::Iter<'buf, Token<'src, T>>>;

    type IterElem = std::slice::Iter<'buf, Token<'src, T>>;

    fn iter_indices(&self) -> Self::Iter {
        self.tokens.iter().enumerate()
    }

    fn iter_elements(&self) -> Self::IterElem {
        self.tokens.iter()
    }

    fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(Self::Item) -> bool,
    {
        self.tokens.iter().position(predicate)
    }

    fn slice_index(&self, count: usize) -> Result<usize, nom::Needed> {
        match count <= self.tokens.len() {
            true => Ok(count),
            false => Err(Needed::Unknown),
        }
    }
}

impl<'buf, 'src, T> TokensRef<'buf, 'src, T> {
    /// Constructs a new [`Tokens`] from the given [`Token`] slice.
    pub const fn new(tokens: &'buf [Token<'src, T>]) -> Self {
        Self { tokens }
    }

    /// Returns the length of the underlying token buffer.
    pub fn len(&self) -> usize {
        self.tokens.len()
    }

    /// Returns `true` iff `self.len() == 0`.
    pub fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    /// Returns the first element of `self`, or `None` if it is empty.
    pub fn first(&self) -> Option<&Token<'src, T>> {
        self.tokens.first()
    }

    /// Returns the last element of `self`, or `None` if it is empty.
    pub fn last(&self) -> Option<&Token<'src, T>> {
        self.tokens.last()
    }
}
