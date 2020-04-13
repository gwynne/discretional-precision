// MARK: Base ArbitraryInt type

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
public struct ArbitraryInt {
    
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
    @usableFromInline internal var sign: Bool
    
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

extension ArbitraryInt: SignedInteger {

    // MARK: - Various protocol requirements
    
    /// Counts zero-words in the backing store and multiplies them by the bit
    /// width for efficiency, adding the trailing count from the first non-zero
    /// word (which must exist by our definition of this type unless the total
    /// value is zero). We store signed values in unsigned form, and the
    /// trailing zero bit count of a negative 2's-complement integer is the same
    /// as that of its magnitude, so no extra consideration is required. For a
    /// zero value, we record it as 1 trailing zero bit.
    @inlinable public var trailingZeroBitCount: Int {
        guard storage != [0] else { return 1 }
        let firstNonzeroIndex = storage.firstIndex(where: { $0 != 0 })!
        return (firstNonzeroIndex << Self.radixBitShift) + storage[firstNonzeroIndex].trailingZeroBitCount
    }
    
    /// Override the default `negate()`, otherwise it defaults to `0 - self`,
    /// which would recurse since we implement that in terms of negation. Make
    /// sure not to produce the illegal "negative zero" representation.
    @inlinable public mutating func negate() {
        self.sign = self.storage == [0] ? false : !self.sign
    }
    
    /// Override the default implementation of `signum()` because we can provide
    /// a more efficient answer than `(self > 0) - (self < 0)`.
    @inlinable public func signum() -> ArbitraryInt { storage == [0] ? .zero : (sign ? -1 : 1) }
    
    /// Magnitude is absolute value. Return a negated self if needed.
    @inlinable public var magnitude: ArbitraryInt { sign ? -self : self }
    
    // MARK: - Initializers
    
    /// For any integral value of arbitrary size, make ourselves that size and
    /// copy the raw value directly. (Are there endianness concerns here?)
    @inlinable public init<T>(_ source: T) where T: BinaryInteger {
        if T.self is Self.Type {
            self = unsafeBitCast(source, to: Self.self)
        } else {
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
    
    // MARK: - Utility subscripts
    
    /// Convenience subscript which presents the appearance of an infinite
    /// number of leading zeroes in the storage. Useful when iterating the
    /// digits of two values at once to avoid extra bounds checks.
    internal subscript(infinite i: Storage.Index) -> Storage.Element {
        i >= storage.endIndex ? 0 : storage[i]
    }
    
    // MARK: - Arithmetic operators
    /// Optimize for the case where x is already obviously mod m.
    @inlinable public static func % (x: ArbitraryInt, m: ArbitraryInt) -> ArbitraryInt {
        if x < .zero || x >= m {
            return x.quotientAndRemainder(dividingBy: m).remainder
        } else {
            return x
        }
    }
    
    /// In-place modulo.
    @inlinable public static func %= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs % rhs }

    /// Directly forward to `quotientAndRemainder(dividingBy:)`, taking the
    /// quotient and discarding the remainder.
    @inlinable public static func / (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt { lhs.quotientAndRemainder(dividingBy: rhs).quotient }
    
    /// In-place division.
    @inlinable public static func /= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs / rhs }
    
    /// Directly forward to `product(multipliedBy:)`
    @inlinable public static func * (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt { lhs.product(multipliedBy: rhs) }
    
    /// In-place multiplication
    @inlinable public static func *= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs * rhs }

    /// Directly forward to `difference(subtracting:)`
    @inlinable public static func - (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt { lhs.difference(subtracting: rhs) }
    
    /// In-place subtraction
    @inlinable public static func -= (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs - rhs }

    /// Directly forward to `sum(addedTo:)`
    @inlinable public static func + (lhs: ArbitraryInt, rhs: ArbitraryInt) -> ArbitraryInt { lhs.sum(addedTo: rhs) }
    
    /// In-place addition
    @inlinable public static func += (lhs: inout ArbitraryInt, rhs: ArbitraryInt) { lhs = lhs + rhs }

    // MARK: - Equatable and Comparable
    
    /// `Equatable`. Digits by bitwise compare, and sign must match. (Checking
    /// bit width requires extra work querying the storage array which just
    /// slows things down versus equating it.)
    @inlinable public static func == (lhs: ArbitraryInt, rhs: ArbitraryInt) -> Bool {
        return lhs.storage == rhs.storage && lhs.sign == rhs.sign
    }
    
    /// Comparison operator. Noticeably faster than the default implementation
    /// via `BinaryInteger`.
    @inlinable public static func < (lhs: ArbitraryInt, rhs: ArbitraryInt) -> Bool {
        if lhs.sign && rhs.sign { return -rhs > -lhs } // if both negative, flip the compare
        if lhs.sign != rhs.sign { return lhs.sign } // if only one negative, the negative one is smaller
        if rhs.storage.count > lhs.storage.count { return true }
        if lhs.storage.count > rhs.storage.count { return false }
        
        for i in lhs.storage.indices.reversed() {
            if lhs.storage[i] != rhs.storage[i] { return lhs.storage[i] < rhs.storage[i] }
        }
        return false // they were equal, which means not less than
    }
    
    // MARK: - Bitwise operators
    
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
                (lhs.storage[w], scratch) = ((lhs.storage[w] << remainderBits) | scratch, lhs.storage[w] >> (radixBitWidth - remainderBits))
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
        let (wholeDigitsDropped, bitsDropped) = (Int(exactly: rhs)! >> radixBitShift, Int(exactly: rhs)! & (radixBitWidth - 1))
        if wholeDigitsDropped >= lhs.storage.count { lhs = lhs.sign ? .minusOne : .zero; return }
        // Drop entire digits from the start of the storage list. Much simpler and faster than shifting bits down.
        lhs.storage.removeFirst(wholeDigitsDropped)
        lhs.debug(.RShift, state: ["whole": wholeDigitsDropped, "remBits": bitsDropped])
        lhs.storage[0] >>= bitsDropped // drop remaining bits from first word, leaves gap at top. If bitsDropped == 0, this is wasteful but harmless
        for w in 1..<lhs.storage.count { // repeat for each word, pulling bits from further up and pasting them into the empty area
            lhs.storage[w - 1] |= (lhs.storage[w] & (1 << bitsDropped - 1)) << (radixBitWidth - bitsDropped)
            lhs.storage[w] >>= bitsDropped
        }
        // Drop all trailing zeroes, leaving at least one word in the result.
        while lhs.storage.count > 1 && lhs.storage.last == .zero { lhs.storage.removeLast() }
        lhs.debug(.RShift, state: ["value": lhs])
    }

    /// Unary NOT, flip every single bit. Since this type declares itself as
    /// signed, emulation of two's complement behavior (which we have kept to in
    /// all other operations) requires that the result be `-(x + 1)`, which is
    /// not the same as flipping all the bits in our backing store.
    @inlinable public static prefix func ~ (x: ArbitraryInt) -> ArbitraryInt {
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
    
    // MARK: - GCD and LCM
    
    /// `ax + by = v` where `v = gcd(x, y)`, extended binary algorithm.
    ///
    /// - TODO: This implementation produces INCORRECT values for certain inputs
    ///   I was not yet able to track down what cases cause this; it only showed
    ///   up when attempting to use the results to calculate a modular
    ///   multiplicative inverse.
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
                if A.storage[0] & 0x1 != 0 || B.storage[0] & 0x1 != 0 {
                    (A, B) = (A + y, B - x)
                }
                (A, B) = (A >> 1, B >> 1)
                debug(.GCD, state: ["u": u, "A": A, "B": B], "u%2=0")
            }
            assert(v > .zero)
            while v.storage[0] & 0x1 == 0 {
                v >>= 1
                if C.storage[0] & 0x1 != 0 || D.storage[0] & 0x1 != 0 {
                    (C, D) = (C + y, D - x)
                }
                (C, D) = (C >> 1, D >> 1)
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
    @inlinable public func lcm(_ rhs: ArbitraryInt) -> ArbitraryInt {
        if self == .zero && rhs == .zero { return .zero } // lcm(0, 0) = 0
        return (self * rhs).magnitude / gcd_bin(rhs).v
    }
    
}

// MARK: - ArbitraryInt <-> BinaryInteger etc. operators

/// Additional operator overload signatures to enable various obvious and/or
/// useful interoperability scenarios with various types for various operators.
/// These return their results only as `ArbitraryInt`; doing so avoids a huge
/// amount of consideration of how to best handle what would otherwise be a
/// plethora of out-of-bounds, value overflow, conversion failure, and other
/// such issues. It's also easier on the compiler.
extension ArbitraryInt {

    // Modulus, division, multiplication, subtraction, and addition of
    // arbitrary-precision values of/by/from/to integer values. Also bitwise
    // AND, OR, and XOR operators for same. All versions return the result as an
    // arbitrary-precision value which must be explicitly converted to something
    // else if desired.
    @inlinable public static func % <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs % Self(rhs) }
    @inlinable public static func / <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs / Self(rhs) }
    @inlinable public static func * <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs * Self(rhs) }
    @inlinable public static func - <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs - Self(rhs) }
    @inlinable public static func + <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs + Self(rhs) }
    @inlinable public static func & <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs & Self(rhs) }
    @inlinable public static func | <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs | Self(rhs) }
    @inlinable public static func ^ <RHS>(lhs: ArbitraryInt, rhs: RHS) -> ArbitraryInt where RHS: BinaryInteger { lhs ^ Self(rhs) }

    // Shorthand self-assignment versions of the eight operators above.
    @inlinable public static func %= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs %= Self(rhs) }
    @inlinable public static func /= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs /= Self(rhs) }
    @inlinable public static func *= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs *= Self(rhs) }
    @inlinable public static func -= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs -= Self(rhs) }
    @inlinable public static func += <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs += Self(rhs) }
    @inlinable public static func &= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs &= Self(rhs) }
    @inlinable public static func |= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs |= Self(rhs) }
    @inlinable public static func ^= <RHS>(lhs: inout ArbitraryInt, rhs: RHS) where RHS: BinaryInteger { lhs ^= Self(rhs) }

}
