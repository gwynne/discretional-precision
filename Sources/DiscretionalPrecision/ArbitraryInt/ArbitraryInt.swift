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
public struct ArbitraryInt: SignedInteger, LosslessStringConvertible {
    
    /// Typealias for our internal storage, which does _not_ conform to the
    /// expectations of `BinaryInteger.Words`, and is easier to type multiple
    /// times than the array form, especially given the funky way Xcode insists
    /// on "helping out" when typing delimiters of any kind. This, like the
    /// storage itself, is `internal` instead of `private` to support the
    /// splitting of the implementation across many files and to support the
    /// storage being `@usableFromInline`.
    @usableFromInline internal typealias Storage = Array<UInt>
    
    /// The raw 64-bit "digits" in LSW->MSW order, representing in combination
    /// all the bits of the arbitrary-precision value. Each individual digit is
    /// stored in machine-native endianness (so, little endian). One of these
    /// values is conceptually exactly one digit in base `b` (see the `radix`
    /// property), where `b` is `1 << UInt.bitWidth`. The implications of a
    /// base-18-quintillion numbering system are quite interesting, for sure.
    /// `internal` instead of `private` to support the implementation of this
    /// type being spread over many files, and also so it can be usable from
    /// inline for performance.
    @usableFromInline internal var storage: Storage
    
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
    
    /// We support arbitrary widths, not just "arbitrary widths that are
    /// multiples of 64". As a result, the correct bit width of the value is not
    /// an entirely trivial value, nor is fixed across mutations. We could store
    /// the calculated value as an optimization, but making the calculation
    /// itself inlinable should be sufficiently performant so long as the
    /// optimizer can be trusted to coalesce multiple invocations. A value of
    /// zero has bit width 1, which must be handled specially.
    /// See `BinaryInteger.bitWidth`.
    @inlinable public var bitWidth: Int { Swift.max(1, (self.storage.count << Self.radixBitShift) - self.storage.last!.leadingZeroBitCount) }

    /// Internal utility initializer for very fast construction. The assertions
    /// which guarantee correctness of the representation are present in this
    /// initializer, but only fire in debug builds.
    @usableFromInline internal init(storage: Storage, sign: Bool) {
        self.storage = storage
        self.sign = sign
        assert(!self.storage.isEmpty) // There must be at least one digit.
        assert(self.storage.last! != 0 || (self.storage.count == 1 && self.sign == false)) // The last digit must be non-zero unless it's alone and positive.
    }
    
}

extension ArbitraryInt {

    /// We implement a signed representation. Unlike the fixed-width integer
    /// types, this type has no unsigned counterpart; the effective range of an
    /// instance of this type is unlimited, and the storage requirements of
    /// positive and negative values are identical, so a separate unsigned type
    /// would serve very little purpose.
    /// See `BinaryInteger.isSigned`.
    @inlinable public static var isSigned: Bool { true }
    
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
        if self.bitWidth < Self.radixBitWidth { return "\(sign ? "-" : "")\(storage[0].hexEncodedString())" }
        
        // We flip the endianness and display the word array in MSW-first order
        // to yield a representation which largely corresponds to the
        // serialization format used by OpenSSL's `bn` library.
        return "\(self.sign ? "-" : "")\(self.storage.reversed().map { $0.hexEncodedString(prefix: false) }.joined())"
    }
    
    /// Counts zero-words in the backing store and multiplies them by the bit
    /// width for efficiency, adding the trailing count from the first non-zero
    /// word (which must exist by our definition of this type unless the total
    /// value is zero). We store signed values in unsigned form, and the
    /// trailing zero bit count of a negative 2's-complement integer is the same
    /// as that of its magnitude, so no extra consideration is required. For a
    /// zero value, we record it as 1 trailing zero bit.
    public var trailingZeroBitCount: Int {
        guard storage != [0] else { return 1 }
        let firstNonzeroIndex = storage.firstIndex(where: { $0 != 0 })!
        return (firstNonzeroIndex << Self.radixBitShift) + storage[firstNonzeroIndex].trailingZeroBitCount
    }
    
    /// Override the default `negate()`, otherwise it defaults to `0 - self`,
    /// which would recurse since we implement that in terms of negation.
    @inlinable public mutating func negate() {
        self.sign = self.storage == [0] ? false : !self.sign
    }
    
    /// Override the default implementation of `signum()` because we can provide
    /// a more efficient answer than `(self > 0) - (self < 0)`.
    @inlinable public func signum() -> ArbitraryInt { storage == [0] ? .zero : (sign ? -1 : 1) }
    
    /// Magnitude is absolute value. Return a negated self if needed.
    @inlinable public var magnitude: ArbitraryInt { sign ? -self : self }
    
    /// For any integral value of arbitrary size, make ourselves that size and
    /// copy the raw value directly. (Are there endianness concerns here?)
    public init<T>(_ source: T) where T: BinaryInteger {
        if T.self is Self.Type {
            self = unsafeBitCast(source, to: Self.self)
        } else {
            guard source.magnitude.bitWidth > 0 else { fatalError("Nonsensical bit width!") }
            self.init(storage: .init(source.magnitude.words), sign: source.signum() < 0)
        }
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
        self.init(storage: hexWords, sign: hexSign)
    }
    
    /// The number of bits in a single one of our digits, e.g. the bit width of
    /// our radix `b`.
    internal static var radixBitWidth: Int = Words.Element.bitWidth
    
    /// The logarithm base 2 of the `radixBitWidth`, useful for optimizing use
    /// of the value via bit shifting.
    internal static var radixBitShift: Int = Self.radixBitWidth.trailingZeroBitCount
    
    /// The radix base `b` of our digits; e.g. `1 << radixBitWidth`.
    internal static var radix: ArbitraryInt = .one << Self.radixBitWidth
 
    /// Convenience subscript overloads for the individual digits in the
    /// `storage` array. Permits fine control over bounds checking and
    /// defaulted values.
    internal subscript(i: Storage.Index) -> Storage.Element { get { storage[i] } set { storage[i] = newValue } } // direct forward
    internal subscript<R: RangeExpression>(r: R) -> Storage.SubSequence where R.Bound == Storage.Index { storage[r] } // direct forward
    internal subscript(infinite i: Storage.Index) -> Storage.Element { i >= storage.endIndex ? 0 : storage[i] } // implicit pad on right to `Index.max`
    internal subscript(infinite r: PartialRangeFrom<Storage.Index>) -> FlattenSequence<[AnySequence<Storage.Element>]> { // implicit pad on right to infinity
        [AnySequence(storage[r]), AnySequence(sequence(first: 0, next: { _ in 0 }))].joined()
    }
    internal subscript(unsafe i: Storage.Index) -> Storage.Element { storage.indices.contains(i) ? storage[i] : 0 } // zero for ANY out of bounds index, use with care
    internal subscript<R: BoundedRangeExpression>(unsafe r: R) -> FlattenSequence<[AnySequence<Storage.Element>]> where R.Bound == Storage.Index { // pads out of bound edges with zeroes on both sides, use with care
        [AnySequence(repeatElement(0, count: Swift.max(storage.startIndex - r.lowerBound, 0))),
            AnySequence(storage[r.relative(to: storage).clamped(to: storage.startIndex..<storage.endIndex)]),
        AnySequence(repeatElement(0, count: Swift.max(r.upperBound - storage.endIndex - 1, 0)))].joined()
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
            return (quotient: ArbitraryInt(storage: [q], sign: self.sign != rhs.sign && q != 0), remainder: ArbitraryInt(storage: [r], sign: self.sign && r != 0))
        }
        
        var x = self.magnitude, y = rhs.magnitude
        let λ = Swift.max(y.storage.last!.leadingZeroBitCount - 1, 0)
        (x, y) = (x << λ, y << λ) // normalize
        let n = x.storage.endIndex - 1, t = y.storage.endIndex - 1
        var q = Storage(repeating: 0, count: n - t + 1)
        let ybnt = (y << ((n - t) << Self.radixBitShift))
        
        debug(.Quot, state: ["λ": λ, "n": n, "t": t])
        debug(.Quot, state: ["x": x, "y": y, "ybnt": ybnt])
        while x >= ybnt {
            q[n - t] += 1
            x -= ybnt
            debug(.Quot, state: ["q[n - t]": q[n - t], "x": x], "x >= ybnt")
        }
        for i in stride(from: n, to: t, by: -1) {
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
            let y2 = ArbitraryInt(storage: Array(y[unsafe: (t - 1)...t]).normalized(), sign: false)
            let x3 = ArbitraryInt(storage: Array(x[unsafe: (i - 2)...i]).normalized(), sign: false)
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
        let qq = ArbitraryInt(storage: q.normalized(), sign: self.sign != rhs.sign && q.normalized() != [0])
        debug(.Quot, state: ["λr": λr, "r": r, "q": q.hexEncodedString()])
        debug(.Quot, state: ["quotient": qq, "remainder": ArbitraryInt(storage: r.storage, sign: self.sign)])
        return (quotient: qq, remainder: ArbitraryInt(storage: r.storage, sign: self.sign))
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
        assert(lhs.storage.count < UInt(Int.max) && rhs.storage.count < UInt(Int.max))
        
        let n = lhs.storage.endIndex, t = rhs.storage.endIndex
        var w = Storage(repeating: 0, count: n + t), v = Storage.Element(0)
        var carry1 = false, carry2 = false
        
        lhs.debug(.Prod, state: ["n": n, "t": t])
        for i in 0..<t {
            for j in 0..<n {
                (w[i &+ j], carry2) = w[i &+ j].addingReportingOverflow(w[i &+ n])
                (w[i &+ n], v) = lhs.storage[j].multipliedFullWidth(by: rhs.storage[i])
                (w[i &+ j], carry1) = w[i &+ j].addingReportingOverflow(v)
                w[i &+ n] &+= (carry1 ? 1 : 0) &+ (carry2 ? 1 : 0)
            }
            lhs.debug(.Prod, state: ["i": i, "w": w.hexEncodedString()])
        }
        while w.last == 0 { w.removeLast() }
        let product = ArbitraryInt(storage: w, sign: lhs.sign != rhs.sign)
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
        // Therefore subtraction per below may always assume positive numbers and last-place borrowing.

        var n = lhs.storage.count, result = Storage(repeating: 0, count: n), borrow = Storage.Element.zero
        
        // Subtract each group of bits in sequence with propagated borrow.
        for i in 0..<n {
            lhs.debug(.Diff, state: ["lWord": lhs[i].hexEncodedString(), "rWord": rhs[infinite: i].hexEncodedString(), "borrow": borrow])
            (borrow, result[i]) = rhs[infinite: i].subtractingPreservingCarry(from: lhs[i], carryin: borrow)
            lhs.debug(.Diff, state: ["lWord - rWord": result[i].hexEncodedString(), "borrow": borrow])
        }
        // Given rhs < lhs (already checked), taking a borrow out of the last word is illegal.
        assert(borrow == .zero)
        // Drop all trailing zero digits of the results array, making sure to leave at least one.
        while result.count > 1 && result.last == .zero { result.removeLast() }
        // Return result as `ArbitraryInt`
        let difference = ArbitraryInt(storage: result, sign: false)
        difference.debug(.Diff, state: ["difference": difference])
        return difference
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
        let n = lhs.storage.endIndex, t = rhs.storage.endIndex, z = Swift.max(n, t)
        var result = Storage(repeating: 0, count: z), carry = Storage.Element.zero
        
        lhs.debug(.Sum, state: ["n": n, "t": t, "z": z])
        for i in 0..<z { (carry, result[i]) = lhs[infinite: i].addedPreservingCarry(to: rhs[infinite: i], carryin: carry) }
        lhs.debug(.Sum, state: ["result[0..<z]": result.hexEncodedString(), "carry": carry])
        if carry != .zero { result.append(carry) }
        assert(result.normalized() == result)
        lhs.debug(.Sum, state: ["sum": ArbitraryInt(storage: result, sign: false)])
        return ArbitraryInt(storage: result, sign: false)
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
        let n = lhs.storage.endIndex, t = rhs.storage.endIndex, z = Swift.max(n, t)
        var carry = Storage.Element.zero
        
        lhs.debug(.Sum, state: ["n": n, "t": t, "z": z], "inplace!")
        lhs.storage.append(contentsOf: Array(repeating: Storage.Element.zero, count: Swift.max(t - n, 0)))
        for i in 0..<z { (carry, lhs[i]) = lhs[i].addedPreservingCarry(to: rhs[infinite: i], carryin: carry) }
        if carry != .zero { lhs.storage.append(carry) }
        lhs.debug(.Sum, state: ["lhs[0..<n+t]": lhs.storage.hexEncodedString(), "carry": carry], "inplace!")
        lhs.debug(.Sum, state: ["sum": lhs], "inplace!")
    }
    
    /// `Equatable`. Digits by bitwise compare, and sign must match. (Checking
    /// bit width requires extra work querying the storage array which just
    /// slows things down versus equating it.)
    public static func == (lhs: ArbitraryInt, rhs: ArbitraryInt) -> Bool {
        return lhs.storage == rhs.storage && lhs.sign == rhs.sign
    }
    
    /// Comparison operator. Noticeably faster than the default implementation
    /// via `BinaryInteger`.
    public static func < (lhs: ArbitraryInt, rhs: ArbitraryInt) -> Bool {
        if lhs.sign && rhs.sign { return -rhs > -lhs } // if both negative, flip the compare
        if lhs.sign != rhs.sign { return lhs.sign } // if only one negative, the negative one is smaller
        if rhs.storage.count > lhs.storage.count { return true }
        if lhs.storage.count > rhs.storage.count { return false }
        
        for i in lhs.storage.indices.reversed() {
            if lhs.storage[i] != rhs.storage[i] { return lhs.storage[i] < rhs.storage[i] }
        }
        return false // they were equal, which means not less than
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
    /// the same operation on our unsigned storage regardless. Shifting by a
    /// negative value is equivalent to shifting the absolute of that value in
    /// the other direction, apparently.
    public static func <<= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger {
        lhs.debug(.LShift, state: ["x": lhs, "y": rhs])
        guard rhs >= .zero else { lhs >>= rhs.magnitude; return }
        guard rhs > .zero, lhs != .zero else { return } // shifting a zero bit count or shifting a lot of zeroes does nothing
        precondition(rhs < (lhs.bitWidth << 50), "Asked to shift an absurd number of bits into an arbitrary-precision value.")
        let (wholeDigitsShifted, remainderBits) = (Int(exactly: rhs)! >> radixBitShift, Int(exactly: rhs)! & (radixBitWidth - 1))
        
        // Insert n / Storage.Element.bitSize digits at the start. Saves cascading potentially hundreds of bytes of data
        // and ensures the cascade logic never has to deal with more than one digit's worth of bits at a time.
        lhs.storage.insert(contentsOf: Storage(repeating: 0, count: wholeDigitsShifted), at: lhs.storage.startIndex)
        lhs.debug(.LShift, state: ["whole": wholeDigitsShifted, "remBits": remainderBits])
        // If the remainder was zero, the shift count was an exact multiple of the word bit width, nothing to do!
        if remainderBits > 0 {
            // Make sure the last word has enough spare bits, add a new one if not. Only one extra is needed at most.
            // Note: Our bit width only counts to the last 1 bit, leading 0 bits are extra capacity.
            if lhs.storage.last!.leadingZeroBitCount < remainderBits { lhs.storage.append(0) }
            // Skip as many zeroes in our storage as possible, no need to cascade those. Round to the nearest word bounday.
            let startWordIdx = lhs.trailingZeroBitCount >> radixBitShift
            assert(startWordIdx < lhs.storage.count, "Check for lhs == 0 failed?")
            // Go through each word, saving bits off the top and shifting bits in from the bottom. If we did it right,
            // we'll end with the scrach data containing the zeroes at the top of the last word.
            var scratch = Storage.Element(0) // scratch space for bits destined for the next word
            for w in startWordIdx..<lhs.storage.count {
                // List/tuple assignments evaluate rvalue elements left to right, then assign lvalue elements left to right.
                // Exactly equivalent to writing `let (newWord, save) = /*rvalue*/; lhs.storage = newWord; scratch = save`.
                // In the end only saves an extra `let`, but it looks kinda neat. Sorta.
                (lhs[w], scratch) = ((lhs[w] << remainderBits) | scratch, lhs[w] >> (radixBitWidth - remainderBits))
            }
            assert(scratch == 0, "Data was left in scratch after left-shift bit cascading. Bad math?")
        }
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
        let (wholeDigitsDropped, bitsDropped) = (Int(exactly: rhs)! >> radixBitShift, Int(exactly: rhs)! & (radixBitWidth - 1))
        // Drop entire digits from the start of the storage list. Much simpler and faster than shifting bits down.
        lhs.storage.removeFirst(wholeDigitsDropped)
        lhs.debug(.RShift, state: ["whole": wholeDigitsDropped, "remBits": bitsDropped])
        lhs[0] >>= bitsDropped // drop remaining bits from first word, leaves gap at top. If bitsDropped == 0, this is wasteful but harmless
        for w in 1..<lhs.storage.count { // repeat for each word, pulling bits from further up and pasting them into the empty area
            lhs[w - 1] |= (lhs[w] & (1 << bitsDropped - 1)) << (radixBitWidth - bitsDropped)
            lhs[w] >>= bitsDropped
        }
        // Drop all trailing zeroes, leaving at least one word in the result.
        while lhs.storage.count > 1 && lhs.storage.last == .zero { lhs.storage.removeLast() }
        lhs.debug(.RShift, state: ["value": lhs])
    }

    /// Unary NOT, flip every single bit. Since this type declares itself as
    /// signed, emulation of two's complement behavior (which we have kept to in
    /// all other operations) requires that the result be `-(x + 1)`, which is
    /// not the same as flipping all the bits in our backing store.
    public static prefix func ~ (x: ArbitraryInt) -> ArbitraryInt {
        return -(x + .one)
    }

    /// Perform a bitwise AND operation of all significant bits of `lhs` with
    /// all significant bits of `rhs`, padding with zeroes on the MSB end if one
    /// has more bits than the other, and recalculating the total bit width of
    /// the result based on the highest bit still set therein. The operation is
    /// performed on the raw bits as if both values were unsigned. The sign of
    /// the result is the outcome of taking the bitwise AND of both inputs' sign
    /// flags, represened as single sign bits (in other words, the result is
    /// positive unless both inputs were negative). An exception exists if the
    /// magnitude of the result is zero; "negative zero" is not a valid
    /// representation.
    public static func &= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.storage = (0..<Swift.max(lhs.storage.count, rhs.storage.count)).map { lhs[infinite: $0] & rhs[infinite: $0] }.normalized()
        lhs.sign = lhs.sign && rhs.sign && lhs != .zero
    }

    /// Perform a bitwise OR operation of all significant bits of `lhs` with all
    /// significant bits of `rhs`, padding with zeroes on the MSB end if one has
    /// more bits than the other, and recalculating the total bit width of the
    /// result based on the highest bit still set therein. The operation is
    /// performed on the raw bits as if both values were unsigned. The sign of
    /// the result is the outcome of taking the bitwise OR of both inputs' sign
    /// flags, represened as single sign bits (in other words, the result is
    /// negative unless both inputs were positive). An exception exists if the
    /// magnitude of the result is zero; "negative zero" is not a valid
    /// representation.
    public static func |= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.storage = (0..<Swift.max(lhs.storage.count, rhs.storage.count)).map { lhs[infinite: $0] | rhs[infinite: $0] }.normalized()
        lhs.sign = (lhs.sign || rhs.sign) && lhs != .zero
    }
    
    /// Perform a bitwise XOR operation of all significant bits of `lhs` with all
    /// significant bits of `rhs`, padding with zeroes on the MSB end if one has
    /// more bits than the other, and recalculating the total bit width of the
    /// result based on the highest bit still set therein. The operation is
    /// performed on the raw bits as if both values were unsigned. The sign of
    /// the result is the outcome of taking the bitwise XOR of both inputs' sign
    /// flags, represened as single sign bits (in other words, the result is
    /// negative if the signs of the inputs differ). An exception exists if the
    /// magnitude of the result is zero; "negative zero" is not a valid
    /// representation.
    public static func ^= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) {
        lhs.storage = (0..<Swift.max(lhs.storage.count, rhs.storage.count)).map { lhs[infinite: $0] ^ rhs[infinite: $0] }.normalized()
        lhs.sign = (lhs.sign != rhs.sign) && lhs != .zero
    }
    
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
            while u.storage[0] & 0x1 == 0 {
                u >>= 1
                (A, B) = ((A + ((A & 0x1) == 0 && (B & 0x1) == 0 ? 0 : y)) >> 1, (B - ((A & 0x1) == 0 && (B & 0x1) == 0 ? 0 : x)) >> 1)
                debug(.GCD, state: ["u": u, "A": A, "B": B], "u%2=0")
            }
            assert(v > .zero)
            while v.storage[0] & 0x1 == 0 {
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
