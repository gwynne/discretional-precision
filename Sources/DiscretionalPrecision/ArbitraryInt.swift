import Darwin

/// The precedence of the modular exponentiation operator (see below). Because
/// it'd be a pain to place it precisely where it really belongs, we just stick
/// it at the top of the multiplication operator set and let that be close
/// enough for normal usage. Parenthesis are there if they're needed.
precedencegroup ModularExponentiationPrecedence {
    higherThan: MultiplicationPrecedence
    lowerThan: BitwiseShiftPrecedence
    associativity: left
}

/// The precdecence of the simple and combining exponentiation operator (see
/// below). It sits at the top of the current precedence set, partially because
/// it needs to bind very tightly with both operands in order to work properly
/// when used in combining form with the modular combining operator, but also
/// because mathematically exponentiation _does_ have a higher precedence than
/// just about everything else in common usage.
precedencegroup ExponentiationPrecedence {
    higherThan: BitwiseShiftPrecedence
    associativity: right
}

/// For various reasons, we've defined two operators in support of the various
/// operations going on in this file. The first happens to be of general-purpose
/// use in its own right: The exponentiation operator, `✱✱`. (Please note this
/// operator is composed of two U+2731 HEAVY ASTERISK characters, _not_ standard
/// ASCII asterisks. For comparison, a normal asterisk: `*`, versus the heavy
/// codepoint: `✱`). The `✱✱` operator is placed between a base `b` and exponent
/// `e`. Either or both operands may be `BinaryInteger` or `BinaryFloatingPoint`
/// values, though some rounding error and precision loss may occur if care is
/// not take. The oeprator performs simple exponentiation in the traditional
/// form `𝑏⁰ = 1, 𝑏¹ = 𝑏, bⁿ⁺¹ = 𝑏ⁿ · 𝑏`, etc. (Floating-point inputs are handled
/// differently, of course; these are integer equations.) As per the mathematical
/// definition of the exponentiation operation, the operator is
/// _right_-associative, meaning that an expression of the form `a ✱✱ b ✱✱ c` is
/// equivalent to `a ✱✱ (b ✱✱ c)` - since exponentiation is also not
/// commutative, it is important to bear this in mind. It is unfortunate that
/// Swift can not bear the use of a superscript combining modifier as an
/// operator, which would enable the more familiar "power tower" notation.
/// (While it would certainly be possible to use one of the various "up arrow"
/// code points to implement Knuth's up-arrow notation for tetration, that seems
/// to be as far as it is likely to be possible to go. It is not clear that
/// Unicode would be capable of expressing the wide horizontal underline-type
/// curly bracket notation used for hyperoperation at all, much less in Swift.)
infix operator ✱✱: ExponentiationPrecedence

/// The second operator defined here is more purpose-built. In conjunction with
/// the exponentiation operator, it performs the _modular exponentiation_
/// operation defined by:
///
///     𝑐 = 𝑏ᵉ 𝘮𝘰𝘥 𝑚
///
/// Given a base `b`, exponent `e`, and divisor (more often called "modulus")
/// `m`, the modular exponentiation operation raises `b` to the power `e`,
/// divides the result by `m`, and finds the remainder `c` according to the
/// rules of modular arithmetic. As an infix operator only has two operands, and
/// this operation requires three inputs, this implementation defines both the
/// exponentiation operator and a new combining modulus operator. The choice of
/// a second new operator rather than attempting to reuse the existing `%`
/// modulo oeprator was the obvious result of considering the difficulties of
/// working according to Swift's type inference and operator resolution rules.
///
/// The modular combining operator is defined as `↳%↲` (that's U+2183 DOWNWARDS
/// ARROW WITH TIP RIGHTWARDS, a percent sign, and U+2182 DOWNWARDS ARROW WITH
/// TIP LEFTWARDS). It is designed specifically to combine a complete
/// exponentiation expression using `✱✱` with a modulus value. When this
/// combination, and only this combination, appears, the exponentiation operator
/// will yield an instance of a private structure type, containing its two
/// inputs unmodified. This type serves as a sentinel value witin the
/// typesystem, serving to create what is effectively a trinary expression. The
/// `_ModularExponentiationLeftHandSideInput` structure is valid input - indeed,
/// the _only_ valid input, to the modular combining operator. When the
/// resulting faux-tertiary expression is evaluated, the combining operator will
/// perform an optimized modular exponentiation reduction algorithm to calculate
/// the value of `c` with high efficiency for values of large arbitrary
/// precision, such as cryptographic keys. The goal is to enable cryptographic
/// primitives such as RSA encryption in reasonable time. The operator may
/// choose to use more naive/straightfowrard means to calculate the result when
/// the inputs are fixed-width, however, as modular exponentiation often
/// sacrifices accuracy and speed at small scale in the service of both at large
/// scale. A reasonable trade-off, to be sure.
///
/// - Note: The symbol ≡ (U+2261 IDENTICAL TO) appears often in connection with
///   the modular exponentiation operation, in reference to congruence
///   relations. See Wikipedia for more information.

/// - Note: It would have been preferable to use operators that more properly
///   represent their functions, in the vein of `𝑏ⁿ` for exponentiation, or maybe
///   something using the U+2217 ASTERISK OEPRATOR code point. Unfortunately,
///   between the limitations of Unicode fonts, the resrictions on of Swift's
///   allowed set of characters for use as operators, and Xcode's particular
///   weaknesses of text layout, `✱✱` and `↳%↲` were ultimately found to be
///   quite reasonable by compare to some other options. If it had been possible
///   to work with more Unicode esoterica, such as `ρεμ`, well, at least it
///   would have spelled `𝐫ʳ𝐞ᵉ𝐦ᵐ` in _some_ font and language.
///
infix operator ↳%↲: ModularExponentiationPrecedence

public func ✱✱ <LHS, RHS>(_ lhs: LHS, _ rhs: RHS) -> ArbitraryInt where LHS: BinaryInteger, RHS: BinaryInteger {
    return ArbitraryInt(lhs) ✱✱ ArbitraryInt(rhs)
}

/// Performs simple right-to-left binary exponentiation. Runs in, very very
/// approximately, `O(1.5 * log n)` time, where `n` is the number of nonzero
/// bits in `e`.
public func ✱✱ (_ lhs: ArbitraryInt, _ rhs: ArbitraryInt) -> ArbitraryInt {
    if lhs == .zero { return .zero }
    if lhs == .one { return .one }
    lhs.debug(.Exp, state: ["b": lhs, "e": rhs], "rtl binary")
    var S = lhs, e = rhs, A = ArbitraryInt.one
    
    while e != .zero {
        if (e[0] & 0x1) != 0 {
            A *= S
        }
        e >>= 1
        if e != 0 {
            S *= S
        }
        lhs.debug(.Exp, state: ["e": e])
    }
    return A
}

public struct ByteaExponentiation { let base, exp: ArbitraryInt }
public func ✱✱ (_ lhs: ArbitraryInt, _ rhs: ArbitraryInt) -> ByteaExponentiation {
    return .init(base: lhs, exp: rhs)
}

public func ↳%↲(_ lhs: ByteaExponentiation, _ rhs: ArbitraryInt) -> ArbitraryInt {
    if rhs[0] & 0x1 != 0 {
        return lhs.base.montgomeryExponentiation(e: lhs.exp, m: rhs)
    } else {
        return (lhs.base ✱✱ lhs.exp) % rhs
    }
}

protocol BoundedRangeExpression: RangeExpression, Sequence {
    var lowerBound: Bound { get }
    var upperBound: Bound { get }
    func clamped(to limits: Self) -> Self
    init(_ other: Range<Bound>)
    init(_ other: ClosedRange<Bound>)
}
extension Range: BoundedRangeExpression where Bound: Strideable, Bound.Stride: SignedInteger { init(_ other: Range<Bound>) { self = other } }
extension ClosedRange: BoundedRangeExpression where Bound: Strideable, Bound.Stride: SignedInteger { init(_ other: ClosedRange<Bound>) { self = other } }

/// As a `SignedIntger`, we implement `BinaryInteger`, `SignedNumeric`,
/// `Numeric`, `AdditiveArithmetic`, `Equatable`, `ExpressibleByIntegerLiteral`,
/// `CustomStringConvertible`, `Hashable`, and `Strideable`. A lot of this comes
/// for free via defaulted implementations, but not all of those implementations
/// are efficient, desireable, or even functional in all cases.
///
/// We explicitly are _not_ a `FixedWidthInteger` type; our `bitWidth` is not
/// constant between all instances or even within one instance.
///
/// Surprisingly, `Comparable` is not in the list. It seems that its presence is
/// more or less implicit on numeric types, and that the comparison operators
/// work regardless, whether you implement them type-specificallly or not.
public struct ArbitraryInt: SignedInteger, CustomDebugStringConvertible, LosslessStringConvertible {

    /// We reimplement `zero` in terms of a static instance via our internal
    /// memberwise initializer, which is noticeably faster than the default
    /// implementation on `AdditiveArithmetic`, which routes through the
    /// `ExpressibleByIntegerLiteral` .
    /// See `AdditiveArithmetic.zero`.
    public static let zero: ArbitraryInt = .init(words: [0], sign: false, bitWidth: 1)
    
    /// A `one` that's probably a bit faster than getting it from `Int`.
    public static let one: ArbitraryInt = .init(words: [1], sign: false, bitWidth: 1)
    
    /// A `minusOne` that's probably a bit faster than getting it from `Int`.
    public static let minusOne: ArbitraryInt = .init(words: [1], sign: true, bitWidth: 1)
    
    /// We implement a signed representation. There is, in fact, no
    /// corresponding unsigned representation.
    /// See `BinaryInteger.isSigned`.
    @inlinable public static var isSigned: Bool { true }
    
    /// The raw 64-bit words in LSW->MSW order, representing in combination
    /// all the bits of the arbitrary-precision value. Each individual word is
    /// stored in machine-native endianness (so, little endian). One of these
    /// words is conceptually exactly one "digit" in base `b` (see the `radix`
    /// property), where `b` is `1 << UInt.bitWidth`. The implications of a
    /// base-18-quintillion numbering system are quite interesting, for sure.
    /// See `BinaryInteger.words`.
    public var words: [UInt]
    
    /// The sign flag of a given arbitrary-precision integer. Signed values are
    /// stored the same way as unsigned ones, aside this flag. This is basically
    /// sign-magnitude representation, except that we explicitly forbid the
    /// negative zero representation as invalid to avoid ambiguity. This was
    /// chosen versus two's complement (or even one's complement) because it
    /// involves the least amount of monkeying around with our representation
    /// possible to do signed operations. It turns out compensating manually for
    /// a sign flag is still easier than maintaining two's complement when the
    /// bit width of the value isn't fixed.
    public var sign: Bool
    
    /// Since we support arbitrary widths, not "arbitrary widths that are
    /// multiples of 64", we need to separately track our current total bit
    /// width so we can ignore the top `words.count * UInt.bitWidth - bitWidth`
    /// bits. Otherwise this would be computed as N words * UInt bits. Notably,
    /// this can be unambiguously computed by examining `words` (as long as the
    /// array has been correctly normalized), but we maintain the separate value
    /// regardless as an optimization and as a consistency cross-check.
    /// See `BinaryInteger.bitWidth`.
    public var bitWidth: Int
    
    /// Override the default `CustomStringConvertible` conformance; it produces
    /// some very slow results. According to the API contract of integer types,
    /// this conformance must return a string corresponding to the _decimal_
    /// representation of the number. However, as you get into the 2048-bit and
    /// higher realm, such a representation becomes quite a chore to generate.
    /// It's considerably easier to generate a hexadecimal representation, so
    /// we've chosen that as the default way to represent values of this type
    /// as strings. It's convenient that a hex representation tends to be
    /// slightly more semantically useful at extremely high bit widths.
    public var description: String {
        if self == .zero { return "0" }
        if self.bitWidth < Self.radixBitWidth { return "\(sign ? "-" : "")\(words[0].hexEncodedString())" }
        
        // We flip the endianness and display the word array in LSW-first order
        // to yield a representation which largely corresponds to the
        // serialization format used by OpenSSL's `bn` library.
        return "\(self.sign ? "-" : "")0x\(self.words.map { $0.bigEndian.hexEncodedString(prefix: false) }.joined())"
    }
    
    /// A more structured, debugging-friendly visual representation.
    public var debugDescription: String {
        return "\(self.sign ? "-" : "")\(self.words.hexEncodedString()) [\(self.bitWidth)]"
    }
    
    /// Counts zero-words in the backing store and multiplies them by the bit
    /// width for efficiency, adding the trailing count from the first non-zero
    /// word (which must exist by our definition of this type unless the total
    /// value is zero). We store signed values in unsigned form, and the
    /// trailing zero bit count of a negative 2's-complement integer is the same
    /// as that of its magnitude, so no extra consideration is required. For a
    /// zero value, we record it as 1 trailing zero bit.
    public var trailingZeroBitCount: Int {
        guard words != [0] else { return 1 }
        let firstNonzeroIndex = words.firstIndex(where: { $0 != 0 })!
        return (firstNonzeroIndex << Self.radixBitShift) + words[firstNonzeroIndex].trailingZeroBitCount
    }
    
    /// Override the default `negate()`, otherwise it defaults to `0 - self`,
    /// which would recurse since we implement that in terms of negation.
    @inlinable public mutating func negate() {
        self.sign = self.words == [0] ? false : !self.sign
    }
    
    /// Override the default implementation of `signum()` because we can provide
    /// a more efficient answer than `(self > 0) - (self < 0)`.
    @inlinable public func signum() -> ArbitraryInt { words == [0] ? .zero : (sign ? -1 : 1) }
    
    /// Magnitude is absolute value. Return a negated self if needed.
    @inlinable public var magnitude: ArbitraryInt { sign ? -self : self }
    
    /// For any integral value of arbitrary size, make ourselves that size and
    /// copy the raw value directly. (Are there endianness concerns here?)
    public init<T>(_ source: T) where T: BinaryInteger {
        guard source.magnitude.bitWidth > 0 else { fatalError("Nonsensical bit width!") }
        self.init(words: source.magnitude.words, sign: source.signum() < 0)
    }
    
    /// We can represent any integral value of arbitrary size exactly.
    @inlinable public init?<T>(exactly source: T) where T: BinaryInteger { self.init(source) }
    
    /// Arbitrary-width values never need to truncate, reduces to `.init(_:)`.
    @inlinable public init<T>(truncatingIfNeeded source: T) where T: BinaryInteger { self.init(source) }

    /// Arbitrary-width values have no maximum, reduces to `.init(_:)`.
    @inlinable public init<T>(clamping source: T) where T : BinaryInteger { self.init(source) }
    
    /// Convert floating-point values of arbitrary bit width by taking absolute
    /// value, rounding towards zero to chop fractional part, and deferring to
    /// exact value conversion from there. Bypass it for exactly zero values.
    public init<T>(_ source: T) where T : BinaryFloatingPoint {
        let prepped = source.magnitude.rounded(.towardZero)
        guard !prepped.isZero else { self.init(0); return }
        self.init(exactly: prepped)!
    }
    
    /// Convert floating-point value of arbitrary bit width by rotating the
    /// significand left by the number of bits counted by the unbiased exponent.
    /// This yields the effective bit width of the significand. The input is
    /// assumed to be `.isNormal`. 2**exponent is added to the result to un-hide
    /// the 53rd significand bit. Refuses values whose rounded absolute value is
    /// not exactly equal to the original value.
    public init?<T>(exactly source: T) where T : BinaryFloatingPoint {
        let absSource = source.magnitude
        guard absSource.rounded(.towardZero).isEqual(to: absSource) else { return nil }
        let integralPart = (absSource.significandBitPattern >> (T.significandBitCount - Int(absSource.exponent)))
        self.init(Self(integralPart | (1 << absSource.exponent)) * (source.sign.rawValue * -2 + 1))
    }
    
    /// `ExpressibleByIntegerLiteral` conformance. Just forward to `init(_:)`
    @inlinable public init(integerLiteral value: Int64) { self.init(value) }
    
    /// `LosslessStringConvertible` conformance. Attempt to read the format we
    /// output from `description`.
    /// (This is a pretty cheap/lousy implementation.)
    public init?(_ description: String) {
        func chunk<C: Collection>(_ c: C, by size: Int) -> [C.SubSequence] {
            c.indices
                .filter { c.distance(from: c.startIndex, to: $0) % size == 0 }
                .map { c[$0..<(c.index($0, offsetBy: size, limitedBy: c.endIndex) ?? c.endIndex)] }
        }
        func lpadTpo2(_ s: Substring) -> String { s.count % 2 != 0 ? "0\(s)" : String(s) }

        let hexSign = description.first! == "-"
        let hexBytes = chunk(lpadTpo2(description.dropFirst(hexSign ? 1 : 0)), by: 2).map { UInt8($0, radix: 16)! }
        let hexWords = chunk(hexBytes.reversed(), by: 8).map { $0.enumerated().map { UInt($1) << ($0 << 3) }.reduce(0, |).littleEndian }
        self.init(words: hexWords, sign: hexSign)
    }
    
    /// The number of bits in a single one of our digits, e.g. the bit width of
    /// our radix `b`.
    internal static var radixBitWidth: Int = Words.Element.bitWidth
    
    /// The logarithm base 2 of the `radixBitWidth`, useful for optimizing use
    /// of the value via bit shifting.
    internal static var radixBitShift: Int = Int(exactly: log2(Double(exactly: Self.radixBitWidth)!))!
    
    /// The radix base `b` of our digits; e.g. `1 << radixBitWidth`.
    internal static var radix: ArbitraryInt = .one << Self.radixBitWidth
 
    /// An internal utility initializer for very fast construction.
    /// Does not assert as heavily as the usual initializers!
    internal init(words: Words, sign: Bool, bitWidth: Int) {
        self.words = words
        self.sign = sign
        self.bitWidth = bitWidth
        assert(!self.words.isEmpty)
        assert(self.bitWidth == self.bitWidthAsTotalWordBitsMinusLeadingZeroes())
        assert(self.sign == false || (self.words.count > 1 || self[0] != 0))
    }
    
    /// An internal utility initializer not suitable for general use which sets
    /// up a value given an existing array of base-2**64 "digits". Specialized
    /// for when the input array is already of the correct type.
    internal init(words: Words, sign: Bool) {
        precondition(!words.isEmpty)
        precondition(words.count == 1 || words.last! != 0)
        self.init(words: words, sign: sign, bitWidth: Self.bitWidthAsTotalWordBitsMinusLeadingZeroes(of: words))
    }

    /// An internal utility initializer not suitable for general use which sets
    /// up a value given an existing array of base-2**64 "digits".
    internal init<C>(words: C, sign: Bool)  where C: BidirectionalCollection, C.Element == Words.Element {
        self.init(words: Words(words), sign: sign)
    }
    
    /// Convenience subscript overloads for the individual words in the `words`
    /// array. Permits fine control over bounds checking and defaulted values.
    internal subscript(i: Words.Index) -> Words.Element { get { words[i] } set { words[i] = newValue } } // direct forward
    internal subscript<R: RangeExpression>(r: R) -> Words.SubSequence where R.Bound == Words.Index { words[r] } // direct forward
    internal subscript(infinite i: Words.Index) -> Words.Element { i >= words.endIndex ? 0 : words[i] } // implicit pad on right to `Index.max`
    internal subscript(infinite r: PartialRangeFrom<Words.Index>) -> FlattenSequence<[AnySequence<Words.Element>]> { // implicit pad on right to infinity
        [AnySequence(words[r]), AnySequence(sequence(first: 0, next: { _ in 0 }))].joined()
    }
    internal subscript(ghosting i: Words.Index) -> Words.Element { i >= words.startIndex ? words[i] : 0 } // implicit pad on left to `Index.min`
    internal subscript<R: BoundedRangeExpression>(ghosting r: R) -> FlattenSequence<[AnySequence<Words.Element>]> where R.Bound == Words.Index { // implicit pad on left to `r.lowerBound`
        [.init(repeatElement(0, count: Swift.max(words.startIndex - r.lowerBound, 0))), .init(words[r.clamped(to: .init(words.startIndex..<(.max)))])].joined()
    }
    internal subscript(unsafe i: Words.Index) -> Words.Element { words.indices.contains(i) ? words[i] : 0 } // zero for ANY out of bounds index, use with care
    internal subscript<R: BoundedRangeExpression>(unsafe r: R) -> FlattenSequence<[AnySequence<Words.Element>]> where R.Bound == Words.Index { // pads out of bound edges with zeroes on both sides, use with care
        [AnySequence(repeatElement(0, count: Swift.max(words.startIndex - r.lowerBound, 0))),
            AnySequence(words[r.strictlyRelative(to: words)]),
        AnySequence(repeatElement(0, count: Swift.max(r.upperBound - words.endIndex - 1, 0)))].joined()
    }
    
    /// Common implementation for / and %. Override the stdlib implementation
    /// of this to avoid its slow double-divide call while at it.
    public func quotientAndRemainder(dividingBy rhs: ArbitraryInt) -> (quotient: ArbitraryInt, remainder: ArbitraryInt) {
        debug(.Quot, state: ["d": self, "m": rhs])
        guard rhs != .zero else { fatalError("Division by zero") }
        guard self.magnitude >= rhs.magnitude else { return (quotient: .zero, remainder: self) } // divisor>dividend, shortcut result; covers zero property too
        guard rhs != .one else { return (quotient: self, remainder: .zero) } // identity property
        guard rhs != .minusOne else { return (quotient: -self, remainder: .zero) } // negative identity; division by -1 is the unary negation operator
        
        if self.bitWidth <= Self.radixBitWidth && rhs.bitWidth <= (Self.radixBitWidth << 1) {
            let (q, r) = rhs[0].dividingFullWidth((high: self[infinite: 1], low: self[0]))
            return (quotient: ArbitraryInt(words: [q], sign: self.sign != rhs.sign && q != 0), remainder: ArbitraryInt(words: [r], sign: self.sign && r != 0))
        }
        
        var x = self.magnitude, y = rhs.magnitude
        let λ = Swift.max(y.words.last!.leadingZeroBitCount - 1, 0)
        (x, y) = (x << λ, y << λ) // normalize
        let n = x.words.endIndex - 1, t = y.words.endIndex - 1
        var q = Words(repeating: 0, count: n - t + 1)
        let ybnt = (y << ((n - t) << Self.radixBitShift))
        
        debug(.Quot, state: ["λ": λ, "n": n, "t": t])
        debug(.Quot, state: ["x": x, "y": y, "ybnt": ybnt])
        while x >= ybnt {
            q[n - t] += 1
            x -= ybnt
            debug(.Quot, state: ["q[n - t]": q[n - t], "x": x], "x >= ybnt")
        }
        for i in stride(from: n, to: t, by: -1) where t < n {
            let j = i - t - 1
            debug(.Quot, state: ["i": i, "j": j])
            
            if x[infinite: i] == y[t] {
                q[j] = .max
                debug(.Quot, state: ["x[i]": x[infinite: i].hexEncodedString(), "y[t]": y[t].hexEncodedString(), "q[j]": q[j].hexEncodedString()], "x[i] == y[t]")
            } else {
                let res = y[t].dividingFullWidth((high: x[unsafe: i], low: x[unsafe: i - 1]))
                q[j] = res.quotient.magnitude
                debug(.Quot, state: ["x[i-1...i]/y[t]": "\(res.quotient.hexEncodedString()) REM \(res.remainder.hexEncodedString())", "q[j]": q[j].hexEncodedString()])
            }
            let y2 = ArbitraryInt(words: Array(y[unsafe: (t - 1)...t]).normalize(), sign: false)
            let x3 = ArbitraryInt(words: Array(x[unsafe: (i - 2)...i]).normalize(), sign: false)
            debug(.Quot, state: ["y2=y[t-1...t]": y2, "x3=x[i-2...i]": x3])
            while ArbitraryInt(q[j]) * y2 > x3 {
                q[j] -= 1
                debug(.Quot, state: ["q[j] * y2": ArbitraryInt(q[j] + 1) * y2, "q[j]": q[j].hexEncodedString()], "> x3")
            }
            let yb = (y << (j << Self.radixBitShift)), qyb = ArbitraryInt(q[j]) * yb
            x -= qyb
            debug(.Quot, state: ["yb": yb, "qyb": qyb, "x": x])
            if x < 0 {
                x += yb
                q[j] -= 1
                debug(.Quot, state: ["x": x, "q[j]": q[j].hexEncodedString()], "x < 0")
            }
        }
        let λr = x, r = λr >> λ
        let qq = ArbitraryInt(words: q.normalize(), sign: self.sign != rhs.sign && q.normalize() != [0])
        debug(.Quot, state: ["λr": λr, "r": r, "q": q.hexEncodedString()])
        debug(.Quot, state: ["quotient": qq, "remainder": ArbitraryInt(words: r.words, sign: self.sign)])
        return (quotient: qq, remainder: ArbitraryInt(words: r.words, sign: self.sign))
    }
    
    /// Both division and modulo forward to `quotientAndRemainder()`.
    /// Modulo optimizes for the case where x is already obviously mod m.
    public static func % (x: ArbitraryInt, m: ArbitraryInt) -> ArbitraryInt {
        if x < .zero || x >= m {
            return x.quotientAndRemainder(dividingBy: m).remainder
        } else {
            return x
        }
    }
    public static func %= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs % rhs }

    /// Division is a fun one. With arbitrary-precision values, especially those
    /// used for cryptographic algorithms like RSA, one of the more efficient
    /// options is to go directly for a modular exponentiation algorithm such as
    /// the Montgomery Reduction or a right-to-left binary method. Modular
    /// exponentiation, in turn reduces to simple divsion when m = 1. See the
    /// exhaustive commentary (which fortunately maanges to also serve as at
    /// least some small amont of documentation) on the exponentiation `✱✱` and
    /// modular cobining `↳%↲` operators. However, in the end, the fact that we
    /// can treat our numbers as having a radix `b`, where `b` is the bit width
    /// of `UInt`, means we can defer to the standard library's good old
    /// `dividedReportingOverflow(by:)` and simply do "schoolyard" long division
    /// to satisfactorally compute the properly merged results.
    public static func / (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt {
        return lhs.quotientAndRemainder(dividingBy: rhs).quotient
    }
    public static func /= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs / rhs }
    
    /// Multiplication. Even harder to find good answers for than division in
    /// some cases. The Karatsuba algorithm turned out to simply not work
    /// properly despite several earnest attempts; for the time being, we use an
    /// efficient reformulation of traditional "schoolbook" multiplication.
    /// There's an algorithm linked from Wikipedia called the "Harvey-Hoeven
    /// algorithm", which claims to have a downright absurd time complexity of
    /// `O(n log n)` - true or not, there's not a snowball's chance in the
    /// galatic core of me implementing it. I can't even code an FFT without a
    /// pseudocode implementation to reference, and even then I only faintly
    /// grasp the algorithm. This thing uses Gaussian sampling, talks about
    /// computing "complex multidimensional" discrete Fourier transforms, offers
    /// to show "a multivariate generalisation of Bluestein’s algorithm"... I
    /// only understand about every fifth worth in the PDF. Hell, I couldn't
    /// even get my head around the long patient description of Toom-3. So yeah,
    /// no, I'll just suffer through with quadratic until someone better than me
    /// at math comes along or I learn new stuff.
    public static func * (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt {
        lhs.debug(.Prod, state: ["u": lhs, "v": rhs])
        guard lhs != .zero && rhs != .zero else { return .zero } // zero property
        guard lhs != .one else { return rhs } // identity property
        guard rhs != .one else { return lhs } // identity property
        guard lhs != .minusOne else { return -rhs } // negative identity = unary negation
        guard rhs != .minusOne else { return -lhs } // negative identity = unary negation
        assert(lhs.words.count < UInt(Int.max) && rhs.words.count < UInt(Int.max))
        
        let n = lhs.words.endIndex, t = rhs.words.endIndex
        var w = Words(repeating: 0, count: n + t), v = Words.Element(0)
        var carry1 = false, carry2 = false
        
        lhs.debug(.Prod, state: ["n": n, "t": t])
        for i in 0..<t {
            for j in 0..<n {
                (w[i &+ j], carry2) = w[i &+ j].addingReportingOverflow(w[i &+ n])
                (w[i &+ n], v) = lhs.words[j].multipliedFullWidth(by: rhs.words[i])
                (w[i &+ j], carry1) = w[i &+ j].addingReportingOverflow(v)
                w[i &+ n] &+= (carry1 ? 1 : 0) &+ (carry2 ? 1 : 0)
            }
            lhs.debug(.Prod, state: ["i": i, "w": w.hexEncodedString()])
        }
        while w.last == 0 { w.removeLast() }
        let product = ArbitraryInt(words: w, sign: lhs.sign != rhs.sign)
        lhs.debug(.Prod, state: ["product": product])
        return product
    }
    public static func *= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs * rhs }

    /// To simplify subtration, we reformulate operations on negative numbers in
    /// terms of addition whenever possible. Addition, in turn, reformulates its
    /// negative inputs as subtraction when possible as well; the combination of
    /// the various negations in both directions results in a well-defined path
    /// for all inputs with no infinite loops (we hope).
    public static func - (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt {
        lhs.debug(.Diff, state: ["x": lhs, "y": rhs])
        guard lhs != rhs else { return .zero } // optimize the obvious
        guard rhs != .zero else { return lhs }
        guard rhs < lhs else { return -(rhs - lhs) } // auto-commutative property
        if rhs.sign { return (lhs + -rhs) } // if subtrahend is negative, convert to adding the negation
        // if minuend is negative and subtrahend isn't, auto-commutative property takes effect
        // if subtrahend is negative, regardless of minuend, conversion to addition takes effect
        //  5 -  2 -> normal, 2 -  5 -> -(5 - 2), -5 -  2 -> -(2 - -5) -> -(2 + 5), 5 - -2 -> (5 + 2)
        // -2 - -5 -> (-2 + 5), -5 - -2 -> -(-2 - -5) -> -(-2 + 5)
        // Therefore subtration per below may always assume positive numbers and last-place borrowing.

        var result = ArbitraryInt.zero, borrow = false
        
        // Subtract each group of bits in sequence with propagated borrow.
        result.words = (0..<Swift.max(lhs.words.count, rhs.words.count)).map {
            lhs.debug(.Diff, state: ["lWord": lhs[infinite: $0].hexEncodedString(), "rWord": rhs[infinite: $0].hexEncodedString(), "borrow": borrow])
            let r = lhs[infinite: $0].subtractingWithBorrow(rhs[infinite: $0], borrow: &borrow)
            lhs.debug(.Diff, state: ["lWord - rWord": r.hexEncodedString(), "borrow": borrow])
            return r
        }
        // Given rhs < lhs (already checked), taking a borrow out of the lsat word is illegal.
        assert(!borrow)
        // Drop all _trailing_ words of the result that are zero. Ensure at least one remains. TODO: More like what + does.
        result.words = result.words.normalize()
        // Calculate result bit width as the total words bit count minus leading zero bits of last word. Zero value has one bit.
        result.bitWidth = result.bitWidthAsTotalWordBitsMinusLeadingZeroes()
        // Basic sanity assertions on the calculated width
        assert(result.bitWidth <= lhs.bitWidth)
        
        lhs.debug(.Diff, state: ["difference": result])
        return result
    }
    
    /// There's really only the one way to do addition no matter how you slice
    /// it: Digit-at-a-time carry. Each of our digits is radix b, aka a radix of
    /// 18 quintillion. Hell of a lot of possibilities in that ones column!
    /// Tries as hard as it can to avoid allocations and copying.
    public static func + (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt {
        lhs.debug(.Sum, state: ["a": lhs, "b": rhs])
        guard lhs != .zero else { return rhs } // zero property
        guard rhs != .zero else { return lhs } // zero property
        if lhs.sign { return rhs - (-lhs) } // rewrite -a + b as b - a; -5 + -2 -> -(5 + 2), -5 + 2 -> -(5 - 2), -5 + 7 -> 7 - 5
        if rhs.sign { return lhs - (-rhs) } // rewrite a + -b as a - b;  5 + -2 -> 5 - 2, 5 + -7 -> 5 - 7 -> -(7 - 5)

        // If we get here both operands are positive
        let n = lhs.words.endIndex, t = rhs.words.endIndex, z1 = Swift.min(n, t), z2 = Swift.max(n, t)
        var result = Words(repeating: 0, count: z2 + 1), carry = false
        
        lhs.debug(.Sum, state: ["n": n, "t": t, "z1": z1, "z2": z2])
        for i in 0..<z1 { result[i] = lhs[i].addingWithCarry(rhs[i], carry: &carry) }
        lhs.debug(.Sum, state: ["result[0..<z1]": result.hexEncodedString(), "carry": carry])
        for i in z1..<z2 { result[i] = (n > z1 ? lhs : rhs)[i].addingWithCarry(0, carry: &carry) }
        lhs.debug(.Sum, state: ["result[0..<z2]": result.hexEncodedString(), "carry": carry])
        if carry { result[z2 ] = 1 }
        else { _ = result.removeLast() }
        assert(result.normalize() == result)
        lhs.debug(.Sum, state: ["sum": ArbitraryInt(words: result, sign: false)])
        return ArbitraryInt(words: result, sign: false)
    }
    /// The same algorithm as the three-operand form above, but tries even
    /// harder to avoid allocations and copying.
    public static func += (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.debug(.Sum, state: ["a": lhs, "b": rhs], "inplace!")
        guard lhs != .zero else { lhs = rhs; return } // zero property
        guard rhs != .zero else { return } // zero property
        if lhs.sign { lhs = rhs - (-lhs); return } // rewrite -a + b as b - a; -5 + -2 -> -(5 + 2), -5 + 2 -> -(5 - 2), -5 + 7 -> 7 - 5
        if rhs.sign { lhs -= (-rhs); return } // rewrite a + -b as a - b;  5 + -2 -> 5 - 2, 5 + -7 -> 5 - 7 -> -(7 - 5)

        // If we get here both operands are positive
        let n = lhs.words.endIndex, t = rhs.words.endIndex, z1 = Swift.min(n, t)
        var carry = false
        
        lhs.debug(.Sum, state: ["n": n, "t": t, "z1": z1], "inplace!")
        for i in 0..<z1 { lhs[i] = lhs[i].addingWithCarry(rhs[i], carry: &carry) }
        lhs.debug(.Sum, state: ["lhs[0..<z1": lhs[0..<z1].hexEncodedString(), "carry": carry], "inplace!")
        if n > t { for i in t..<n { lhs[i] = lhs[i].addingWithCarry(0, carry: &carry) } }
        else if t > n { for i in n..<t { lhs.words.append(rhs[i].addingWithCarry(0, carry: &carry)) } }
        if carry { lhs.words.append(1) }
        lhs.debug(.Sum, state: ["lhs[0..<n+t]": lhs.words.hexEncodedString(), "carry": carry], "inplace!")
        lhs.bitWidth = lhs.bitWidthAsTotalWordBitsMinusLeadingZeroes()
        lhs.debug(.Sum, state: ["sum": lhs], "inplace!")
    }
    
    /// `Equatable`. Bit width, words by bitwise compare, and sign must match.
    public static func == (lhs: ArbitraryInt, rhs: ArbitraryInt) -> Bool {
        return lhs.bitWidth == rhs.bitWidth && lhs.words == rhs.words && lhs.sign == rhs.sign
    }
    
    /// Comparison operator. Noticeably faster than the default implementation
    /// via `BinaryInteger`.
    public static func < (lhs: ArbitraryInt, rhs: ArbitraryInt) -> Bool {
        if lhs.sign && rhs.sign { return -rhs > -lhs } // if both negative, flip the compare
        if lhs.sign != rhs.sign { return lhs.sign } // if only one negative, the negative one is smaller

        if lhs.bitWidth < rhs.bitWidth { return true }
        if lhs.bitWidth > rhs.bitWidth || lhs == rhs { return false }
        for (lhsWord, rhsWord) in zip(lhs.words, rhs.words).reversed() {
            if lhsWord < rhsWord { return true }
            else if lhsWord > rhsWord { return false }
        }
        fatalError() // if we get here, the == operator is broken
    }
    
    /// Shift the entire value of `lhs` left by `rhs` bits, zero-filling from
    /// the right. This operation effectively adds the number of bits shifted to
    /// the value's bit count (unless the original value was zero, in which case
    /// left-shifting has no effect). Arbitrary-precision values do not lose
    /// high-order bits regardless of how many are shifted in, meaning there is
    /// no practical limit on the number of bits either; even that number can
    /// itself be arbitrary-precision. To prevent memory exhaustion scenarios
    /// and other "ridiculous" behaviors, this implementation will raise a
    /// runtime exception (a precondition failure) if the number of bits
    /// specified by `rhs` would cause growth of the original value by more than
    /// four orders of magnitude. Whether the shifted value is negative is
    /// _ignored_; bit shifting has the effect of multiplying by two, which is
    /// the same operation on our unsigned storage words regardless. Shifting by
    /// a negative value is equivalent to shifting the absolute of that value in
    /// the other direction, apparently.
    public static func <<= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger {
        lhs.debug(.LShift, state: ["x": lhs, "y": rhs])
        guard rhs >= .zero else { lhs >>= rhs.magnitude; return }
        guard rhs > .zero, lhs != .zero else { return } // shifting a zero bit count or shifting a lot of zeroes does nothing
        precondition(rhs < (lhs.bitWidth << 50), "Asked to shift an absurd number of bits into an arbitrary-precision value.")
        let (wholeWordsShifted, remainderBits) = (Int(exactly: rhs)! >> radixBitShift, Int(exactly: rhs)! & (radixBitWidth - 1))
        
        // Insert n / Words.Element.bitSize words at the start. Saves cascading potentially hundreds of bytes of data
        // and ensures the cascade logic never has to deal with more than one word's worth of bits at a time.
        lhs.words.insert(contentsOf: Words(repeating: 0, count: wholeWordsShifted), at: lhs.words.startIndex)
        lhs.debug(.LShift, state: ["whole": wholeWordsShifted, "remBits": remainderBits])
        // If the remainder was zero, the shift count was an exact multiple of the word bit width, nothing to do!
        if remainderBits > 0 {
            // Make sure the last word has enough spare bits, add a new one if not. Only one extra is needed at most.
            // Note: Our bit width only counts to the last 1 bit, leading 0 bits are extra capacity.
            if lhs.words.last!.leadingZeroBitCount < remainderBits { lhs.words.append(0) }
            // Skip as many zeroes in our storage as possible, no need to cascade those. Round to the nearest word bounday.
            let startWordIdx = lhs.trailingZeroBitCount >> radixBitShift
            assert(startWordIdx < lhs.words.count, "Check for lhs == 0 failed?")
            // Go through each word, saving bits off the top and shifting bits in from the bottom. If we did it right,
            // we'll end with the scrach data containing the zeroes at the top of the last word.
            var scratch = Words.Element(0) // scratch space for bits destined for the next word
            for w in startWordIdx..<lhs.words.count {
                // List/tuple assignments evaluate rvalue elements left to right, then assign lvalue elements left to right.
                // Exactly equivalent to writing `let (newWord, save) = /*rvalue*/; lhs.words = newWord; scratch = save`.
                // In the end only saves an extra `let`, but it looks kinda neat. Sorta.
                (lhs[w], scratch) = ((lhs[w] << remainderBits) | scratch, lhs[w] >> (radixBitWidth - remainderBits))
            }
            assert(scratch == 0, "Data was left in scratch after left-shift bit cascading. Bad math?")
        }
        // Update bit width by adding the total number of bits that got shifted in.
        lhs.bitWidth += Int(rhs)
        assert(lhs.bitWidth == lhs.bitWidthAsTotalWordBitsMinusLeadingZeroes(), "We did something wrong, counted bits isn't previous plus shifted")
        lhs.debug(.LShift, state: ["value": lhs])
    }
    
    /// Compared to left-shift, right-shift on arbitrary-precision is actually a
    /// bit simpler, since it's all about dropping data instead of adding it.
    /// Again, shifts by a negative width go in the other direction and
    /// negatives are ignored. Since we are a signed type, maintaining the
    /// illusion that we have a two's complement representation requires making
    /// sure the sign bit retains its value. -2 >> 2 == -1, not zero.
    public static func >>= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger {
        lhs.debug(.RShift, state: ["x": lhs, "y": rhs])
        guard rhs >= .zero else { lhs <<= rhs.magnitude; return }
        guard rhs > .zero, lhs != .zero else { return } // no point shifting by zero or shifting zeroes
        if rhs >= lhs.bitWidth { lhs = lhs.sign ? -1 : .zero; return } // if shifting all bits out, just reset to zero
        let (wholeWordsDropped, bitsDropped) = (Int(exactly: rhs)! >> radixBitShift, Int(exactly: rhs)! & (radixBitWidth - 1))
        // Drop entire words from the start of the words list. Much simpler and faster than shifting bits down.
        lhs.words.removeFirst(wholeWordsDropped)
        lhs.debug(.RShift, state: ["whole": wholeWordsDropped, "remBits": bitsDropped])
        lhs[0] >>= bitsDropped // drop remaining bits from first word, leaves gap at top. If bitsDropped == 0, this is wasteful but harmless
        for w in 1..<lhs.words.count { // repeat for each word, pulling bits from further up and pasting them into the empty area
            lhs[w - 1] |= (lhs[w] & (1 << bitsDropped - 1)) << (radixBitWidth - bitsDropped)
            lhs[w] >>= bitsDropped
        }
        // Update bit width
        lhs.bitWidth -= Int(rhs)
        // Normalize any residual leading zeroes
        lhs.words = lhs.words.normalize()
        assert(lhs.bitWidth == lhs.bitWidthAsTotalWordBitsMinusLeadingZeroes(), "We did something wrong, counted bits isn't bits minus shifted")
        lhs.debug(.RShift, state: ["value": lhs])
    }

    /// Unary NOT, flip every single bit. Since this type declares itself as
    /// signed, emulation of two's complement behavior (which we have kept to in
    /// all other operations) requires that the result be `-(x + 1)`, which is
    /// not the same as flipping all the bits in our backing store.
    public static prefix func ~ (x: ArbitraryInt) -> ArbitraryInt {
        return -(x + .one)
    }

    /// For simplicity's sake, even if it's not necessarily correct, from the
    /// perspective of the bitwise operations, our value is unsigned. Otherwise
    /// considerable ambiguity can arise in what the results should be.
    public static func &= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.words = zip(lhs.words.rpad(with: 0, upTo: rhs.words.count), rhs.words.rpad(with: 0, upTo: lhs.words.count)).map { $0 & $1 }.normalize()
        lhs.bitWidth = lhs.bitWidthAsTotalWordBitsMinusLeadingZeroes()
        lhs.sign = (lhs.words.count == 1 && lhs[0] == 0 ? false : lhs.sign)
    }

    /// For simplicity's sake, even if it's not necessarily correct, from the
    /// perspective of the bitwise operations, our value is unsigned. Otherwise
    /// considerable ambiguity can arise in what the results should be.
    public static func |= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.words = zip(lhs.words.rpad(with: 0, upTo: rhs.words.count), rhs.words.rpad(with: 0, upTo: lhs.words.count)).map { $0 | $1 }.normalize()
        lhs.bitWidth = lhs.bitWidthAsTotalWordBitsMinusLeadingZeroes()
        lhs.sign = (lhs.words.count == 1 && lhs[0] == 0 ? false : lhs.sign)
    }
    
    /// For simplicity's sake, even if it's not necessarily correct, from the
    /// perspective of the bitwise operations, our value is unsigned. Otherwise
    /// considerable ambiguity can arise in what the results should be.
    public static func ^= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.words = zip(lhs.words.rpad(with: 0, upTo: rhs.words.count), rhs.words.rpad(with: 0, upTo: lhs.words.count)).map { $0 ^ $1 }.normalize()
        lhs.bitWidth = lhs.bitWidthAsTotalWordBitsMinusLeadingZeroes()
        lhs.sign = (lhs.words.count == 1 && lhs[0] == 0 ? false : lhs.sign)
    }
    
    private var isEvenGTE2: Bool { self != .zero && self.words[0] & 0x1 == 0 }
    
    /// `ax + by = v` where `v = gcd(x, y)`, extended binary algorithm.
    public func gcd_bin(_ rhs: ArbitraryInt) -> (a: ArbitraryInt, b: ArbitraryInt, v: ArbitraryInt) {
        debug(.GCD, state: ["x": self, "y": rhs])
        guard self != rhs && rhs != .zero else { return (a: .zero, b: .zero, v: self) }
        guard self != .zero else { return (a: .zero, b: .zero, v: rhs) }
        
        let g = Swift.min(self.trailingZeroBitCount, rhs.trailingZeroBitCount)
        let x = self >> g, y = rhs >> g
        var u = x, v = y, A = ArbitraryInt.one, B = ArbitraryInt.zero, C = ArbitraryInt.zero, D = ArbitraryInt.one
        
        debug(.GCD, state: ["x": x, "y": y, "g": g])
        debug(.GCD, state: ["u": u, "v": v, "A": 1, "B": 0, "C": 0, "D": 1])
        repeat {
            assert(u > .zero)
            while u.isEvenGTE2 {
                u >>= 1
                (A, B) = ((A + ((A & 0x1) == 0 && (B & 0x1) == 0 ? 0 : y)) >> 1, (B - ((A & 0x1) == 0 && (B & 0x1) == 0 ? 0 : x)) >> 1)
                debug(.GCD, state: ["u": u, "A": A, "B": B], "u%2=0")
            }
            assert(v > .zero)
            while v.isEvenGTE2 {
                v >>= 1
                (C, D) = ((C + ((C & 0x1) == 0 && (D & 0x1) == 0 ? 0 : y)) >> 1, (D - ((C & 0x1) == 0 && (D & 0x1) == 0 ? 0 : x)) >> 1)
                debug(.GCD, state: ["v": v, "C": C, "D": D], "v%2=0")
            }
            if u >= v {
                (u, A, B) = (u - v, A - C, B - D)
                debug(.GCD, state: ["u": u, "v": v, "A": A, "B": B], "u >= v")
            } else {
                (v, C, D) = (v - u, C - A, D - B)
                debug(.GCD, state: ["u": u, "v": v, "C": C, "D": D], "u <  v")
            }
        } while u != .zero
        debug(.GCD, state: ["a": C, "b": D, "v": v << g])
        assert(C * self + D * rhs == v << g)
        return (a: C, b: D, v: v << g)
    }

    /// Extremely trivial LCM calculation via GCD.
    public func lcm(_ rhs: ArbitraryInt) -> ArbitraryInt {
        if self == .zero && rhs == .zero { return .zero } // lcm(0, 0) = 0
        return (self * rhs).magnitude / gcd_bin(rhs).v
    }
    
    /// Binary extended GCD can also solve for modular multiplicative inverse.
    /// Returns x^-1 mod m. If there is no inverse for this input, returns nil.
    public func inverse(modulo m: ArbitraryInt) -> ArbitraryInt? {
        guard m > .one else { return nil }
        debug(.ModInv, state: ["x": self, "m": m])
        var rn = self % m
        if rn < .zero { rn += m.magnitude }
        var t = ArbitraryInt.zero, tn = ArbitraryInt.one, r = m
        debug(.ModInv, state: ["x(%m)": rn, "t": t, "tn": tn])
        while rn != .zero {
            let (q, rem) = r.quotientAndRemainder(dividingBy: rn)
            debug(.ModInv, state: ["r": r, "rn": rn, "q": q, "rem": rem])
            (t, tn) = (tn, t - q * tn)
            (r, rn) = (rn, r - q * rn)
            debug(.ModInv, state: ["t(=tn)": t, "tn(=t-q*tn)": tn, "r(=rn)": r, "rn(=r-q*rn)": rn])
        }
        if r > .one { return nil }
        if t < .zero { t += m }
        debug(.ModInv, state: ["inv": t])
        return t
    }

    /// Perform Montgomery multiplication, return `xyR^-1 mod m`, whatever that
    /// actually means....
    public func montgomeryReducedProduct(with rhs: ArbitraryInt, mod m: ArbitraryInt, modPrime mP: ArbitraryInt? = nil) -> ArbitraryInt {
        debug(.ModMul, state: ["x": self, "y": rhs, "m": m, "m'": mP ?? .zero])
        guard let mP = mP ?? (-m).inverse(modulo: Self.radix) else { return .minusOne }
        let x = self, y = rhs, n = m.words.count
        var A = Self.zero
        debug(.ModMul, state: ["x": x, "y": y, "n": n, "m'": mP])
        for i in 0..<n {
            let u = ((ArbitraryInt(A[0]) + ArbitraryInt(x[infinite: i]) * ArbitraryInt(y[0])) * mP)[0]
            A = (A + ArbitraryInt(x[infinite: i]) * y + ArbitraryInt(u) * m) >> Self.radixBitWidth
            debug(.ModMul, state: ["i": i, "u": ArbitraryInt(u), "A": A])
        }
        if A >= m { A -= m }
        if A < .zero { A += m }
        debug(.ModMul, state: ["xyR^-1 mod m": A])
        return A
    }
    /*
    public func montgomeryReducedProduct(with rhs: ArbitraryInt, mod m: ArbitraryInt, modPrime mP: ArbitraryInt? = nil) -> ArbitraryInt {
        debug(.ModMul, state: ["x": self, "y": rhs, "m": m, "m'": mP ?? .zero])
        guard let mP = mP ?? (-m).inverse(modulo: Self.radix) else { return .minusOne }
        let x = self, y = rhs, y0 = y & (Self.radix - 1), n = m.words.count
        var A = ArbitraryInt.zero
        debug(.ModMul, state: ["x": x, "y": y, "n": n, "m'": mP])
        for i in 0..<n {
            let xi: ArbitraryInt = (i < x.words.count ? ArbitraryInt(x.words[i]) : .zero)
            let u: ArbitraryInt = (((A & (Self.radix - 1)) + xi * y0) * mP) & (Self.radix - 1)
            A = (A + xi * y + u * m) >> Self.radixBitWidth
            debug(.ModMul, state: ["i": i, "u": ArbitraryInt(u), "A": A])
        }
        if A >= m { A -= m }
        if A < .zero { A += m }
        debug(.ModMul, state: ["xyR^-1 mod m": A])
        return A
    }
    */
    
    /// Perform Montgomery exponentiation, return `x^e mod m`.
    public func montgomeryExponentiation(e: ArbitraryInt, m: ArbitraryInt) -> ArbitraryInt {
        debug(.ModExp, state: ["x": self, "e": e, "m": m])
        var x = (self < .zero ? self % m : self)
        if x < .zero { x += m.magnitude }
        guard x != .zero else { return .zero }
        guard x != .one else { return .one }
        let R = ArbitraryInt.one << (ArbitraryInt(m.words.count) << Self.radixBitShift), t = e.bitWidth
        guard let mP = (-m).inverse(modulo: Self.radix) else { return -1 }
        debug(.ModExp, state: ["m'": mP, "R": R, "t": t, "x": x])
        let xTilde = x.montgomeryReducedProduct(with: (R * R) % m, mod: m, modPrime: mP)
        var A = R % m
        debug(.ModExp, state: ["x~": xTilde, "A": A, "R*R%m": (R * R) % m])
        for i in (0..<t).reversed() {
            A = A.montgomeryReducedProduct(with: A, mod: m, modPrime: mP)
            debug(.ModExp, state: ["i": i, "A*A mod m": A])
            if (e & (ArbitraryInt.one << i)) != .zero {
                A = A.montgomeryReducedProduct(with: xTilde, mod: m, modPrime: mP)
                debug(.ModExp, state: ["i": i, "1 << i": ArbitraryInt.one << i, "e[i]": (e & (ArbitraryInt.one << i)), "A*x~ mod m": A], "e[i] != 0")
            }
        }
        A = A.montgomeryReducedProduct(with: .one, mod: m, modPrime: mP)
        debug(.ModExp, state: ["A*1 mod m": A])
        debug(.ModExp, state: ["value": A])
        return A
    }

    /// Calculate the total number of bits occupied by `self.words` (simple
    /// multiply), and subtract the number of leading zero bits on the last word
    /// in the list. There must always be at least one word. If the value of all
    /// words is zero, the bit width is `1` (the 0 bit that represents the zero
    /// value itself - 0 bits doesn't represent anything).
    private func bitWidthAsTotalWordBitsMinusLeadingZeroes() -> Int {
        let totalWordBits = self.words.count << Self.radixBitShift
        let lastLeadingZeroBits = self.words.last!.leadingZeroBitCount
        
        // max(1, ...) ensures we never return zero.
        return Swift.max(1, totalWordBits - lastLeadingZeroBits)
    }

    /// Calculate the total number of bits occupied by a given potential `words`
    /// input (simple multiply), and subtract the number of leading zero bits on
    /// the last word in the list. There must always be at least one word. If
    /// the value of all words is zero, the bit width is `1` (the 0 bit that
    /// represents the zero value itself - 0 bits doesn't represent anything).
    private static func bitWidthAsTotalWordBitsMinusLeadingZeroes(of words: Words) -> Int {
        let totalWordBits = words.count << Self.radixBitShift
        let lastLeadingZeroBits = words.last!.leadingZeroBitCount
        
        // max(1, ...) ensures we never return zero.
        return Swift.max(1, totalWordBits - lastLeadingZeroBits)
    }

    /// Debugging facility - this enum needs to be outside the `#if` so there
    /// doesn't end up needing to be a directive at every point of use.
    enum DebugOp: String, CaseIterable, Hashable {
        case Sum, Prod, Quot, ModMul, ModExp, Exp, ModInv, GCD, LShift1, LShift, RShift
        case Diff
    }
    #if DEBUG
    func debug(_ op: DebugOp, state: @autoclosure () -> [String: Any], _ message: @autoclosure() -> String? = nil) {
        guard Self._debugOps.contains(op) else { return }
        let state = state()
        let message = message()
        let s1 = !state.isEmpty ? " " : ""
        let s2 = message != nil ? " " : ""
        print("\(op.rawValue):\(s1)\(state.map { "\($0) = \(String(debugDescribing: $1))" }.joined(separator: ", "))\(s2)\(message ?? "")")
    }
    
    static var _debugOps: Set<DebugOp> = []
    static func debugOn(_ op: DebugOp) { _debugOps.insert(op) }
    static func debugOff(_ op: DebugOp) { _debugOps.remove(op) }
    #else
    func debug(_ op: DebugOp, state: @autoclosure () -> [String: Any], _ message: @autoclosure() -> String? = nil) {}
    static func debugOn(_ op: DebugOp) {}
    static func debugOff(_ op: DebugOp) {}
    #endif
}

extension String {
    public init(debugDescribing subject: Any) {
        if let debugConvertible = subject as? CustomDebugStringConvertible {
            self = debugConvertible.debugDescription
        } else {
            self.init(describing: subject)
        }
    }
}
// MARK: - ArbitraryInt <-> BinaryInteger etc. operators

// Additional operator overload signatures to enable various obvious and/or
// useful interoperability scenarios with various types for various operators.
// Almost also type-interoperating overloads return their results only as
// `ArbitraryInt`. Doing so avoids a huge amount of consideration of how to best
// handle the inevitabe plethora of out-of-bounds, value overflow, conversion
// failure, and other such issues which would be involved in providing a less
// restricted matrix of overloads. It's also easier on the compiler.
//
// Some of these have to actually be on the type, others have to not be.
// Extensions try to keep it straight where possible.

extension ArbitraryInt {
    // Modulus, division, multiplication, subtraction, and addition of
    // arbitrary-precision values of/by/from/to integer values. Also bitwise
    // AND, OR, and XOR operators for same. All versions return the result as an
    // arbitrary-precision value which must be explicitly converted to something
    // else if desired.
    public static func % <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs % Self(rhs) }
    public static func / <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs / Self(rhs) }
    public static func * <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs * Self(rhs) }
    public static func - <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs - Self(rhs) }
    public static func + <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs + Self(rhs) }
    public static func & <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs & Self(rhs) }
    public static func | <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs | Self(rhs) }
    public static func ^ <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs ^ Self(rhs) }

    // Shorthand self-assignment versions of the eight operators above. Same
    // semantics, but integers are only supported on the right hand side. It isn't
    // our job to provide these operators for other types anyhow.
    public static func %= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs %= Self(rhs) }
    public static func /= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs /= Self(rhs) }
    public static func *= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs *= Self(rhs) }
    public static func -= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs -= Self(rhs) }
    public static func += <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs += Self(rhs) }
    public static func &= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs &= Self(rhs) }
    public static func |= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs |= Self(rhs) }
    public static func ^= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs ^= Self(rhs) }
}

extension FixedWidthInteger where Self: UnsignedInteger {
    
    /// Performs an operation similar to `addingReportingOverflow(_:)`, in that
    /// addition is performed, and overflow is checked and reported. However,
    /// instead of simply returning the overflow flag, this routine attempts to
    /// behave similarly to the 8086 Intel assembly language instruction ADC,
    /// "ADd with Carry". This instruction, which still appears in Intel CPUs to
    /// this day, performs addition, but treats the CPU's Carry Flag as both an
    /// input and an output, adding its value (always one or zero) to the result
    /// and including its effect on possible overflow when resetting it to
    /// reflect the current operation. Likewise, this method will honor the
    /// value passed in the `carry` parameter. If `true`, the initial output
    /// value for the sum of the inputs will be set to 1 instead of zero. `self`
    /// is then added to the input, followed by `rhs`, with overflow being
    /// detected both times. If _either_ operation overflowed, the `carry` flag
    /// is set to `true`; otherwise it is reset to `false`. It is expected that
    /// callers will continually pass in the same variable over and over as part
    /// of the process of summing a larger-precision value than `Self` is able
    /// to hold by performing the addition on `Self`-sized chunks at a time. The
    /// behavior of integers guarantees that the value needing to be carried
    /// from one subset of bits to the next (the carry) can never be anything
    /// other than exactly zero ro exactly one - mathematically, in any given
    /// base B, the maximum possible result of any addition between two single-
    /// digit numbers of that radix is 2(B - 1); any additional carry value can
    /// have a maximal result of 2B - 1. (This is in fact the only way for an
    /// addition in any one radix place to produce the digit B - 1 in that
    /// place.) In binary, the possible results are:
    ///     A   B  CF
    ///   - 0 + 0 + 0 = 00, result is 0 bit, no carry
    ///   - 0 + 0 + 1 = 01, result is 1 bit, no carry
    ///   - 0 + 1 + 0 = 01, result is 1 bit, no carry
    ///   - 0 + 1 + 1 = 10, result is 0 bit with carry
    ///   - 1 + 0 + 0 = 01, result is 0 bit, no carry
    ///   - 1 + 0 + 1 = 10, result is 0 bit with carry
    ///   - 1 + 1 + 0 = 10, result is 0 bit with carry
    ///   - 1 + 1 + 1 = 11, result is 1 bit with carry
    ///
    /// - WARNING: After the final call to this method for a given input set, be
    ///   sure to check the final state of the carry flag to see if an
    ///   additional high bit of result needs to be recorded!
    public func addingWithCarry(_ rhs: Self, carry: inout Bool) -> Self {
        var output: Self = carry ? 1 : 0
        var lhsOverflow = false, rhsOverflow = false
        
        (output, lhsOverflow) = output.addingReportingOverflow(self)
        (output, rhsOverflow) = output.addingReportingOverflow(rhs)
        carry = lhsOverflow || rhsOverflow
        return output
    }
    
    /// The same as `addingWithCarry(_:carry:)`, long-winded explanation and
    /// all, but instead of adding it's subtracting, instead of a carry it's a
    /// borrow, and instead of an `ADC` instruction it's a "SuBtract with
    /// Borrow" (`SBB`) instruction. Of course, actually _applying_ a borrow
    /// correctly, especially on unsigned numbers, is a bit harder, but oh well.
    /// As with a carry, the `borrow` flag serves as an additional 1-bit input
    /// operand; if set, one is subtracted from `self` as the first step. The
    /// flag will be reset to indicate whether either that or the subtraction of
    /// `rhs` resulted in overflow (well, underflow). If so, a "schoolbook"
    /// borrow is assumed; the final result is computed as if an additional
    /// value equivalent to the radix base of the inputs (calculated by taking
    /// the partial value resulting from the overflow and subsequent wraparound
    /// behavior) had been added to the minuend (after any borrow was
    /// subtracted). The value of the borrow flag on output must be propagated.
    public func subtractingWithBorrow(_ rhs: Self, borrow: inout Bool) -> Self {
        // Or we could avoid a hell of a lot of mucking about and just do it an obvious way.
        
        // Apply borrow to self, if self isn't already zero (if it is, don't bother).
        let lhs = self >= 0 && borrow ? self &- 1 : self
        
        // Subtract with overflow reporting; the resulting partial value is the correct output.
        let (output, newBorrow) = lhs.subtractingReportingOverflow(rhs)
        
        //print("self = \(self.hexEncodedString()), lhs = \(lhs.hexEncodedString()), rhs = \(rhs.hexEncodedString()), output = \(output.hexEncodedString())")
        //print("borrow = \(borrow), newBorrow = \(newBorrow)")

        // Set borrow on output if it was set on input and self is zero, or if overflow occurred.
        borrow = (borrow && self == 0) || newBorrow
        
        // That's it.
        return output
    }
}

extension BidirectionalCollection where Element: BinaryInteger {
    
    /// If the receiver's `count` is less than the desired count, return a
    /// sequence formed by appending `desiredCount - count` copies of `value`
    /// to `self`. Returns `self` if the count equals or exceeds the desired
    /// number already.
    public func rpad(with value: Element, upTo desiredCount: Int) -> Array<Element> {
        self + Array(repeating: value, count: Swift.max(0, desiredCount - self.count))
    }
    
    /// If the receiver's `count` is less than the desired count, return a
    /// sequence formed by PREpending `desiredCount - count` copies of `value`
    /// to `self`. Returns `self` if the count equals or exceeds the desired
    /// number already.
    public func lpad(with value: Element, upTo desiredCount: Int) -> Array<Element> {
        Array(repeating: value, count: Swift.max(0, desiredCount - self.count)) + self
    }
    
    public func normalize() -> Array<Element> {
        var zeroIdx = self.index(before: self.endIndex)
        while zeroIdx > self.startIndex && self[zeroIdx] == 0 { zeroIdx = self.index(before: zeroIdx) }
        if zeroIdx == self.startIndex && self[self.startIndex] == 0 { return [0] }
        return Array(self[self.startIndex...zeroIdx])
        //guard let zeroes = self.reversed().firstIndex(where: { $0 != 0 }) else { return [0] }
        //return Array(self.dropLast(zeroes))
        //Array(self.reversed().drop(while: { $0 == 0 }).reversed()).rpad(with: 0, upTo: 1)
    }
    
    func hexEncodedString() -> String { "[\(self.map { $0.hexEncodedString() }.joined(separator: ", "))]" }
    
}

extension RangeExpression {

    func strictlyRelative<C>(to collection: C) -> Range<Self.Bound> where C : Collection, Self.Bound == C.Index {
        return self.relative(to: collection).clamped(to: collection.startIndex..<collection.endIndex)
    }

}

// Version of + operator less optimized for memory but somewhat more readable:
/*
static func + (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt {
    let lhsWordsPad = lhs.words.rpad(with: 0, upTo: rhs.words.count), rhsWordsPad = rhs.words.rpad(with: 0, upTo: lhs.words.count)
    var result = ArbitraryInt()
    // Add each group of bits in sequence, propagating the carry flag.
    result.words = zip(lhsWordsPad, rhsWordsPad).map { $0.addingWithCarry($1, carry: &carry) }
    // If last add carried out of the previous highest bit, add a new one.
    if carry { result.words.append(1) }
    // Width of the result will be the greater of the addends', plus the value of the carry flag.
    // (except, not so much)
    result.bitWidth = result.bitWidthAsTotalWordBitsMinusLeadingZeroes() //max(lhs.bitWidth, rhs.bitWidth) + (carry ? 1 : 0)
    // Cross-check that the width value makes sense by re-calculating it as the number of storage words
    // times their width, minus the number of unused bits on the final word.
    //assert(result.bitWidthAsTotalWordBitsMinusLeadingZeroes() == result.bitWidth)
    return result
}
*/

// Failed implementation of the extended binary GCD algorithm.
/*
func gcd(_ rhs: ArbitraryInt) -> (a: ArbitraryInt, b: ArbitraryInt, v: ArbitraryInt) {
    var g = ArbitraryInt.one, x = self, y = rhs
    
    while x & 0x1 == 0 && x != 0 && y & 0x1 == 0 && y != 0 {
        (x, y, g) = (x >> 1, y >> 1, g << 1)
    }
    
    var u = x, v = y, A = ArbitraryInt.one, B = ArbitraryInt.zero, C = ArbitraryInt.zero, D = ArbitraryInt.one
    
    print("GCD: x = \(x), y = \(y)")
    repeat {
        while (u & 0x1) == 0 && u != 0 {
            u >>= 1
            if (A - B) & 0x1 == 0 && A != 0 && B != 0 {
                (A, B) = (A >> 1, B >> 1)
            } else {
                (A, B) = ((A + y) >> 1, (B - x) >> 1)
            }
            print("GCD: u = \(u), A = \(A), B = \(B)")
        }
        while (v & 0x1) == 0 && v != 0 {
            v >>= 1
            if (C - D) & 0x1 == 0 && C != 0 && D != 0 {
                (C, D) = (C >> 1, D >> 1)
            } else {
                (C, D) = ((C + y) >> 1, (D - x) >> 1)
            }
            print("GCD: v = \(v), C = \(C), D = \(D), C & 0x1 = \(C & 0x1), D & 0x1 = \(D & 0x1), C == 0 \(C == 0), D == 0 \(D == 0)")
        }
        if u >= v {
            (u, A, B) = (u - v, A - C, B - D)
        } else {
            (v, C, D) = (v - u, C - A, D - B)
        }
        print("GCD: u = \(u), v = \(v), A = \(A), B = \(B), C = \(C), D = \(D)")
    } while u != 0
    return (a: C, b: D, v: g * v)
}
*/

// Version of modular multiplicative inverse that works but can't handle arbitrary precision.
/*
    public func inverse(modulo m: ArbitraryInt) -> ArbitraryInt? {
        guard m > 1 else { return nil }
        debug(.ModInv, state: ["x": self, "m": m])
        var t = ArbitraryInt.zero, tn = ArbitraryInt.one, r = m, rn = self
        while rn != 0 {
            let q = r / rn
            debug(.ModInv, state: ["t": t, "tn": tn, "r": r, "rn": rn, "q": q])
            (t, tn) = (tn, t - q * tn)
            (r, rn) = (rn, r - q * rn)
        }
        debug(.ModInv, state: ["t": t, "tn": tn, "r": r, "rn": rn])
        if r > 1 { return nil }
        if t < 0 { t += m }
        debug(.ModInv, state: ["inv": t])
        return t
    }
*/