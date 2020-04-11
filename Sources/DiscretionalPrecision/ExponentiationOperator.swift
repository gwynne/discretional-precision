// MARK: - Exponentiation precedence and operator definitions

/// A precdecence group for the exponentiation operator (see below). Per the
/// order of operations in modern algebraic notation, exponentiation is higher
/// precedence than multiplifcation (if curious about the myriad details behind
/// these rules, look up the term "hyperoperation"). Since the bitwise shift
/// operators, mathematically speaking, are just a specialized form of
/// multiplication, exponentiation outranks them as well. This puts it at the
/// extreme top of the operator precedence hiearchy in Swift at the time of this
/// writing. Exponentiation is right- associative (so `xy²` is `x(y²)`, not
/// `(xy)²`). If root extraction and logarithmization operators are ever
/// defined, they would share this precedence and associativity, just as
/// division shares multiplication's.
precedencegroup ExponentiationPrecedence {
    higherThan: BitwiseShiftPrecedence
    associativity: right
}

/// The exponentiation operator. If the underlying data types are capable of
/// overflow and an overflow occurs, a runtime trap is triggered. The `**`
/// (double asterisk) notation is used by, among others, Ada, Bash, COBOL,
/// Fortran, JavaScript, Perl, PHP, Python, Ruby, Haskell, and Spotlight's
/// built-in calculator. This seemed to qualify as a fairly solid expanse of
/// support over both time and space on which to base a naming choice.
infix operator **: ExponentiationPrecedence

/// The overflow exponentiation operator. Identical to `**` except if overflow
/// can and does occur, there is no trap and the result is silently truncated.
infix operator &**: ExponentiationPrecedence

/// An alternative exponentiation operator, having exactly the same semantics,
/// precedence, and behaviors. It can be considered the operator equivalent of
/// a typealias for `**`. Why have it at all, considering it hasn't been in
/// common use since Algol, Commodore BASIC, and TRS-80 BASIC? Because in this
/// author's opinion, it looks rather more neat and tidy than the double-
/// asterisk operator. Also, since Swift doesn't support the use of any form of
/// superscript codepoint, combining or otherwise, for operators, and `^` is
/// already taken by XOR, it's as close to an actual mathematical notation for
/// exponentiation as one can reasonably reach. (Technically, this is Knuth's
/// up-arrow notation, which uses `↑` for exponentiation, `↑↑` for tetration,
/// `↑↑↑` for pentation, and so forth.)
///
/// - Note: The character is `U+2191 UPWARDS ARROW`.
infix operator ↑: ExponentiationPrecedence

/// The corresponding alternative overflow operator for `&**`.
infix operator &↑: ExponentiationPrecedence

// MARK: - Implementation of FixedWidthInteger-based exponentiation

extension FixedWidthInteger {

    /// An implementation of the exponentiation operation for any
    /// `FixedWidthInteger` base, using a fairly simplistic right-to-left binary
    /// algorithm as necessary. offering a very approximate time complexity of
    /// (1.5 log n),` given `n` as the bitwise population count of the exponent
    /// `e`. `e` does not have to be the same type as `self`. The output value
    /// will be the same type as `Self` and be confined to the same range of
    /// representation. If an overflow occurs, the result is the first
    /// `Self`-sized "word" of the full value (which may be very long for some
    /// inputs), truncated to its own bit width, and a `true` overflow flag.
    /// Otherwise, the result is complete and the overflow flag remains `false`
    /// on return.
    ///
    /// - Note: The exponent value does not have to be a `FixedWidthInteger`; it
    ///   only has to conform to `BinaryInteger`.
    ///
    /// - Note: This, like the various "`<something>ReportingOverflow()`"
    ///   methods already present on `FixedWidthInteger`, is an override point
    ///   for _all_ exponentiation operations. All operators and methods using
    ///   exponentiation must bottleneck through this entry point.
    ///
    /// - Note: `ArbitraryInt` is not compatible with this and related
    ///   definitions, as it does not confrom to `FixedWidthInteger` and can not
    ///   overflow. Additional type-specific overloads will be available to
    ///   provide the functionality.
    public func raisedReportingOverflow<RHS>(to e_: RHS) -> (partialValue: Self, overflow: Bool) where RHS: BinaryInteger {
        guard self != .zero && self != 1 else { return (partialValue: self, overflow: false) }
        var S = self, A = Self(1), e = e_
        
        while e != .zero {
            if e & 0x1 != .zero {
                let (partialA, overflow) = A.multipliedReportingOverflow(by: S)
                guard !overflow else { return (partialValue: partialA, overflow: true) }
                A = partialA
            }
            e >>= 1
            if e != .zero {
                let (partialS, overflow) = S.multipliedReportingOverflow(by: S)
                guard !overflow else { return (partialValue: A, overflow: true) }
                S = partialS
            }
        }
        return (partialValue: A, overflow: false)
    }

    /// Define `**` for a base of any `FixedWidthInteger` type and an exponent
    /// also of any `BinaryInteger` type. The two types may be identical but do
    /// not have to be. The result has the same type as the first input (the
    /// base), such that the base defines how large a value can be represented
    /// before overflow occurs.
    public static func ** <RHS>(_ lhs: Self, _ rhs: RHS) -> Self where RHS: BinaryInteger {
        let (value, overflow) = lhs.raisedReportingOverflow(to: rhs)
        guard !overflow else { fatalError() }
        return value
    }
    
    /// Define `&**` identically to `**`, except truncating instead of crashing.
    public static func &** <RHS>(_ lhs: Self, _ rhs: RHS) -> Self where RHS: BinaryInteger {
        return lhs.raisedReportingOverflow(to: rhs).partialValue
    }
    
    /// Alias `↑` to `**`
    public static func ↑ <RHS>(_ lhs: Self, _ rhs: RHS) -> Self where RHS: BinaryInteger { lhs ** rhs }

    /// Alias `&↑` to `&**`
    public static func &↑ <RHS>(_ lhs: Self, _ rhs: RHS) -> Self where RHS: BinaryInteger { lhs &** rhs }

}

// MARK: - Specializations of exponentiation for ArbitraryInt values

extension ArbitraryInt {
    
    /// Define the `**` operator for a base of `ArbitraryInt` type and any
    /// `BinaryInteger` exponent (including but not limited to another
    /// `ArbitraryInt`). Since overflow is not possible, no checking is required
    /// or pefrormed with regards thereto. The time complexity of this
    /// implementation is roughly the same as that of its overflow-checking
    /// counterpart, though it may see a small improvement due to the lack of
    /// checking for overflow (but the improvement in turn is not significant
    /// enough to affect the big-O value, so the point is moot).
    public static func ** <RHS>(_ lhs: Self, _ rhs: RHS) -> Self where RHS: BinaryInteger {
        guard lhs != .zero && lhs != .one else { return lhs }
        var S = lhs, A = Self.one, e = rhs
        
        while e != .zero {
            if e & 0x1 != 0 { A *= S }
            e >>= 1
            if e != .zero { S *= S }
        }
        return A
    }
    
    /// Alias `↑` to `**`
    public static func ↑ <RHS>(_ lhs: Self, _ rhs: RHS) -> Self where RHS: BinaryInteger { lhs ** rhs }
    
    // Note that `&**` and `&↑` only have meaning in an environment having
    // overflow handling semantics, which arbitrary-precision is not, so these
    // operators are not defined on `ArbitraryInt` at all.
}
