extension ArbitraryInt {
    
    /// A version of the `BinaryInteger.Words` structure, taken originally from
    /// the standard library's version in `IntegerTypes.swift.gyb`, which
    /// provides the "always returns 2's complement" semantics required by
    /// `BinaryInteger` by translating the contents of an `ArbitraryInt`'s sign-
    /// magnitude representation on the fly.
    ///
    /// - Warning: It's not entirely clear exactly what 2's complement form
    /// actually _is_ when the bit width of the value is not necessarily a power
    /// of two (or even a multiple of two). Specifically, for negative values,
    /// the sign bit will, more often than not, end up placed at somewhere other
    /// than the MSB of a "word". One-filling the sign bit upwards to the top of
    /// the word it belongs to changes the apparent bit width of the value,
    /// whereas not doing so produces a representation whose sign is not readily
    /// apparently without taking the exact bit width of the original into
    /// account. The implementation chooses the former method, as it is more
    /// clearly a 2's-complement form, and for a caller to decide the correct
    /// number of significant bits requires querying the original value for its
    /// bit width either way.
    public struct Words: RandomAccessCollection {
        public typealias Indices = Range<Int>
        public typealias SubSequence = Slice<ArbitraryInt.Words>
        
        /// The value to which this particular set of `Words` refers.
        /// There appears to be no way to provide the expected semantics of
        /// `Words` without taking a copy of the value, and thus possibly
        /// causing unexpected copying of the value's storage.
        @usableFromInline internal var _value: ArbitraryInt

        @inlinable public init(_ value: ArbitraryInt) {
            self._value = value
            assert(!self.isEmpty) // make sure the value's own representation wasn't corrupt
        }
        
        /// True if an additional word is needed at the end to represent a sign
        /// bit. See discussion above and on `count`.
        @usableFromInline internal var needExtraWordForSignBit: Bool { _value.sign && _value.bitWidth & (ArbitraryInt.radixBitWidth - 1) == 0 }
        
        /// The number of 2's complement "words" needed to represent the value.
        /// This is the same as the number of digits in the value, unless the
        /// value is negative and its last digit uses all its bits, in which
        /// case another word is used to hold the sign bit.
        @inlinable public var count: Int { _value.storage.count + (self.needExtraWordForSignBit ? 1 : 0) }

        @inlinable public var startIndex: Int { 0 }

        @inlinable public var endIndex: Int { count }

        @inlinable public var indices: Indices { startIndex ..< endIndex }
        
        /// The `@_transparent` attribute is copied from the stdlib
        /// version used for generic `BinaryInteger`s. It makes sense for the
        /// compiler to "see through" the method so as to recognize the trivial
        /// increment, enough sense to keep it as a rare "justified" use of
        /// underscored atributes. A habit should not be made of this.
        @_transparent public func index(after i: Int) -> Int { i + 1 }
        
        /// See notes for `index(after:)` above, re: `@_transparent`.
        @_transparent public func index(before i: Int) -> Int { i - 1 }

        @inlinable public subscript(position: Int) -> UInt {
            @inlinable get {
                precondition(position >= 0, "Negative word index")
                precondition(position < endIndex, "Word index out of range")
                if position == endIndex - 1 && needExtraWordForSignBit {
                    return UInt.max // an "extra" word will always have all bits set
                } else if _value.sign {
                    return ~(_value.storage[position] &- ArbitraryInt.Storage.Element(1))
                } else {
                    return _value.storage[position]
                }
            }
        }
    }
    
    @inlinable public var words: Words { Words(self) }

}

extension Array where Element == ArbitraryInt.Words.Element {
    
    public func normalized() -> Array<Element> {
        var zeroIdx = self.index(before: self.endIndex)
        while zeroIdx > self.startIndex && self[zeroIdx] == 0 { zeroIdx = self.index(before: zeroIdx) }
        if zeroIdx == self.startIndex && self[self.startIndex] == 0 { return [0] }
        return Array(self[self.startIndex...zeroIdx])
    }
    
}
