import CDiscretionalClangBuiltins

/// These extensions define "addition with carry" (also expressible as
/// `addingFullWidth`) and "subtraction with borrow" (aka
/// `subtractingFullWidth`). These operations correspond to the Intel `ADC` and
/// `SBB` assembly instructions and can be trivially chained to produce
/// arbitrary-precision arithmetic using only single-precision individual
/// operations, in a similar manner to the standard library's
/// `multipliedFullWidth(by:)` and `dividingFullWidth(by:)` methods. They also
/// correspond to the Clang builtins `__builtin_addc*()` and
/// `__builtin_subc*()`. As with those builtins and as is the general case for
/// these operations, they are defined only for unsigned fixed-width values.
/// (While it is ostensibly possible to define carry and borrow behaviors for
/// arbitrary-precision values, it is unclear what value could be expected to be
/// gained by doing something so recursive.)
extension FixedWidthInteger where Self: UnsignedInteger {

    /// Perform a "full-width" addition, returning the result of adding two
    /// single-precision values as a double-precision value, represented by a
    /// `(high, low)` pair. The behavior and convention match one-to-one with
    /// the semantics of the standard library's `multipliedFullWidth(ny:)`
    /// method, save that the "high" word of the result will always be exactly
    /// zero or exactly one. As with that method, this one can be chained to
    /// add values of arbitrary precision by adding the high word of the result
    /// to the next word of input, ad infinitum.
    ///
    /// - Note: This implementation is generic over any `FixedWidthInteger`
    ///   which is either not one of the builtin types (all of which get their
    ///   own type-specific implementation, see below) or one of said types
    ///   accessed in a sufficiently generic context that the compiler can't
    ///   figure out to invoke the more specific version.
    ///
    /// - Parameter other: The value to add to `self`.
    /// - Parameter carryin: An optionally chained "carry in" value. If chaining
    ///   multiple-precision adds, this would typically be the `high` word
    ///   returned from the previous invocation.
    /// - Returns: A tuple consisting of the "high" word of the result (the
    ///   carryout, expressed as an instance of `Self`) and the "low" word of
    ///   the result (the sum modulo `Self.max + 1`).
    public func addedFullWidth(to other: Self, carryin: Self = Self.zero) -> (high: Self, low: Self.Magnitude) {
        precondition(Self.Magnitude.bitWidth >= Self.bitWidth) // if this is violated, nothing is gonna work right
        
        var result: Self.Magnitude = .zero, carryout: Self = .zero
        
        switch (Self.Magnitude.bitWidth, Self.bitWidth) {
        case (UInt8.Magnitude.bitWidth,  UInt8.bitWidth...):  return UInt8.addedFullWidthConverting(self, to: other, carryin: carryin)
        case (UInt16.Magnitude.bitWidth, UInt16.bitWidth...): return UInt16.addedFullWidthConverting(self, to: other, carryin: carryin)
        case (UInt32.Magnitude.bitWidth, UInt32.bitWidth...): return UInt32.addedFullWidthConverting(self, to: other, carryin: carryin)
        case (UInt64.Magnitude.bitWidth, UInt64.bitWidth...): return UInt64.addedFullWidthConverting(self, to: other, carryin: carryin)
        
        // If all else fails and we find a fixed-width type wider than what we can natively support,
        // or with a bit width not a power of 2 at all, or with a magnitude bit width that doesn't
        // align with Self's bit width (why not?), try doing the multiple precision addition internally,
        // looping over the `UInt`-sized words the two addends contain.
        default:
            // Violation of this rather unobvious precondition results in an incomplete addition. This precondition
            // implicitly requires that `FixedWidthInteger` values always pad their `words` array with zeroes on the
            // most-significant-word end, thus ensuring the requirement expresed here: That `words.count` is equal to
            // `bitWidth / Words.Element.bitWidth` regardless of the leading or trailing zero bit count of the value.
            // To better allow working with types that might have been lazily converted from other types, we only
            // require that one of the inputs meet this condition, not both.
            precondition(Swift.max(self.words.count, other.words.count) ==
                    Self.Magnitude.bitWidth >> Self.Magnitude.Words.Element.Magnitude.bitWidth.trailingZeroBitCount,
                "One or both of the values in a fixed-width multi-precision addition must have a words count matching their bit width."
            )
            
            // Get iterators over the individual words of both operands, and initialize our result words to zero.
            var leftWords = self.words.makeIterator(), rightWords = other.words.makeIterator()
            var leftWord = leftWords.next(), rightWord = rightWords.next()
            var resultWord = Self.Magnitude.Words.Element.zero, carryoutWord = Self.Words.Element.zero
            
            // Keep going as long as either operand still has words left.
            while let _ = leftWord ?? rightWord {
                // Full-width add the left and right words, substituting zero if either operand is out of words.
                (carryoutWord, resultWord) = (leftWord ?? .zero).addedFullWidth(to: rightWord ?? .zero, carryin: carryoutWord)
                // Stuff the new result word into the bottom word of the overall result, then rotate right by one word,
                // effectively "pushing" the new word in at the top of the result. Since we iterate over exactly the
                // number of words the result will contain, we will eventually rotate by exactly that many words, which
                // means the final rotation will place the first result word at the bottom of the result and leave the
                // last word at the top, exactly as desired.
                result = (result | Self.Magnitude(resultWord)) >>> Self.Magnitude.Words.Element.bitWidth
                // Load up the next words as available.
                (leftWord, rightWord) = (leftWords.next(), rightWords.next())
            }
            // Propagate any leftover carryout from the addition chain to the main output, making it the high word of the
            // result and signaling that the final value could not quite be contained within the low word.
            carryout = Self(carryoutWord)
        }

        return (high: carryout, low: result)
    }

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
        
        // Set borrow on output if it was set on input and self is zero, or if overflow occurred.
        borrow = (borrow && self == 0) || newBorrow
        
        // That's it.
        return output
    }
}

extension UInt8 {
    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.addedFullWidth(to:carrying:)` (see above) in all
    /// respects, except that the type of `Self` is concretely known rather than
    /// generically known.
    public func addedFullWidth(to other: Self, carryin: Self = Self.zero) -> (high: Self, low: Self.Magnitude) {
        var carryout = Self.zero
        let result = ClangBuiltins.addcb(x: self, y: other, carryin: carryin, carryout: &carryout)
        return (high: carryout, low: result)
    }
    
    /// Utility method. Accepts an arbitrary unsigned `FixedWidthInteger` type
    /// which is guaranteed by the caller to have a `T.bitWidth` of at least
    /// `Self.bitWidth` and a `T.Magnitude.bitWidth` of exactly
    /// `Self.Magnitude.bitWdith`. Given those guarantees, this method can
    /// forcibly convert the inputs to `Self` and the outputs back to `T`
    /// without (much) concern of a range/bounds violation or other mishap. This
    /// method unfortunately can not be added generically to `FixedWidthInteger`
    /// despite its completely generic nature because `addedFullWidth()` is not
    /// declared on the original protocol, and it will thus be dispatched to
    /// the generic implementation rather than the one on the concrete type
    /// despite `Self` being correct. This would cause an infinite recursion and
    /// crash. Thus we must, annoyingly, duplicate this over and over.
    fileprivate static func addedFullWidthConverting<T>(_ value: T, to other: T, carryin: T = T.zero) -> (high: T, low: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self.init(value).addedFullWidth(to: Self.init(other), carryin: Self.init(carryin))
        return (high: T.init(selfCarryout), low: T.Magnitude.init(selfResult))
    }
}

extension UInt16 {
    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.addedFullWidth(to:carrying:)` (see above) in all
    /// respects, except that the type of `Self` is concretely known rather than
    /// generically known.
    public func addedFullWidth(to other: Self, carryin: Self = Self.zero) -> (high: Self, low: Self.Magnitude) {
        var carryout = Self.zero
        let result = ClangBuiltins.addcs(x: self, y: other, carryin: carryin, carryout: &carryout)
        return (high: carryout, low: result)
    }
    
    /// See `UInt8.addedFullWidthConverting()` for details.
    fileprivate static func addedFullWidthConverting<T>(_ value: T, to other: T, carryin: T = T.zero) -> (high: T, low: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self.init(value).addedFullWidth(to: Self.init(other), carryin: Self.init(carryin))
        return (high: T.init(selfCarryout), low: T.Magnitude.init(selfResult))
    }
}

extension UInt32 {
    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.addedFullWidth(to:carrying:)` (see above) in all
    /// respects, except that the type of `Self` is concretely known rather than
    /// generically known.
    public func addedFullWidth(to other: Self, carryin: Self = Self.zero) -> (high: Self, low: Self.Magnitude) {
        var carryout = Self.zero
        let result = ClangBuiltins.addc(x: self, y: other, carryin: carryin, carryout: &carryout)
        return (high: carryout, low: result)
    }
    
    /// See `UInt8.addedFullWidthConverting()` for details.
    fileprivate static func addedFullWidthConverting<T>(_ value: T, to other: T, carryin: T = T.zero) -> (high: T, low: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self.init(value).addedFullWidth(to: Self.init(other), carryin: Self.init(carryin))
        return (high: T.init(selfCarryout), low: T.Magnitude.init(selfResult))
    }
}

extension UInt64 {
    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.addedFullWidth(to:carrying:)` (see above) in all
    /// respects, except that the type of `Self` is concretely known rather than
    /// generically known.
    public func addedFullWidth(to other: Self, carryin: Self = Self.zero) -> (high: Self, low: Self.Magnitude) {
        var carryout = Self.zero
        let result = ClangBuiltins.addcll(x: self, y: other, carryin: carryin, carryout: &carryout)
        return (high: carryout, low: result)
    }
    
    /// See `UInt8.addedFullWidthConverting()` for details.
    fileprivate static func addedFullWidthConverting<T>(_ value: T, to other: T, carryin: T = T.zero) -> (high: T, low: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self.init(value).addedFullWidth(to: Self.init(other), carryin: Self.init(carryin))
        return (high: T.init(selfCarryout), low: T.Magnitude.init(selfResult))
    }
}

extension UInt {
    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.addedFullWidth(to:carrying:)` (see above) in all
    /// respects, except that the type of `Self` is concretely known rather than
    /// generically known.
    public func addedFullWidth(to other: Self, carryin: Self = Self.zero) -> (high: Self, low: Self.Magnitude) {
        var carryout = Self.zero
        let result = ClangBuiltins.addcl(x: self, y: other, carryin: carryin, carryout: &carryout)
        return (high: carryout, low: result)
    }
}
