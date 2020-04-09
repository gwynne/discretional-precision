/// Trivial 16-entry lookup table of nibbles -> ASCII hex digits
fileprivate let hexTable: [UInt8] = [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66]

extension BinaryInteger {
    
    /// Return a `String` containing a base-16 representation of the integer
    /// value in big-endian order, rendered using lowercase ASCII characters as
    /// an encoding alphabet, and optionally prefixed with the `0x` hexadecimal
    /// indicator. The string is padded on the right with zeroes such that the
    /// string contains exactly `Self.bitWidth + 7 / 8` bits of represented
    /// value (rounded to the nearest byte of width). Integers of arbitrary
    /// bit width are supported, though creating the hex encoding for very large
    /// integers is `O(n)` at best (and may perform noticeably worse due to the
    /// overhead of memory allocation).
    ///
    /// - Parameter prefix: Whether to include the `0x` prefix in the resulting
    ///   string. Defaults to `true`.
    /// - Returns: The hexadecimal string.
    public func hexEncodedString(prefix: Bool = true) -> String {
        "\(prefix ? "0x" : "")\(String(decoding: self.hexEncodedBytes(), as: Unicode.ASCII.self))"
    }
    
    /// Return an array of `UInt8` bytes, each representing a single hexadecimal
    /// digit (1 nibble/4 bits) worth of the value of the integer as a single
    /// ASCII (and thus also UTF-8) codepoint. The array is padded on the far
    /// end with zero digits to `self.bitWidth << 1 + 15 >> 4` (the nearest
    /// byte as two hex digits), and is in big-endian order. Performance for
    /// arbitrary-width integers is approximately `O(n)`. The ASCII alphabet
    /// used is `0123456789abcdef`.
    ///
    /// - Returns: The array of ASCII hexadecimal digits.
    public func hexEncodedBytes() -> [UInt8] {
        // Stride over the bit width in byte-sized chunks, mapping to individual bytes by
        // shift + truncate, then invoke `Sequence.hexEncodedBytes()` to get a final output.
        // The stride is reversed so results appear in big-endian order.
        stride(from: 0, to: self.bitWidth, by: UInt8.bitWidth)
            .lazy
            .reversed()
            .map { UInt8(truncatingIfNeeded: self >> $0) }
            .hexEncodedBytes()
    }
}

extension Sequence where Element == UInt8 {
    /// Transform a `Sequence` of individual bytes into a `String` containing
    /// the hexadecimal representation of each byte in the order they appear in
    /// the sequence. A lowercase ASCII alphabet is used. The result is padded
    /// such that every byte is represented by exactly two hexadecimal digits,
    /// regardless of the number of radix 16 digits naturally occupied by the
    /// value. The `String` is guaranteed to contain only ASCII codepoints.
    ///
    /// - Note: This method is available for `Collection`s as well.
    ///
    /// - Returns: The hexadecimal string.
    public func hexEncodedString() -> String { String(decoding: self.hexEncodedBytes(), as: Unicode.ASCII.self) }
    
    /// Transform a `Sequence` of individual bytes into an array of individual
    /// hexadecimal digits representing those bytes, with two digits of result
    /// appearing for each byte of the input, regardless of the individual
    /// byte's value - for example, `UInt8(0)` is represented as `[0x30, 0x30]`.
    /// Performance is `O(n)` at best but may be worse due to reallocation
    /// overhead for very large `Sequence`s and/or `Sequence`s whose
    /// underestimated count is zero or otherwise significantly understated.
    ///
    /// - Returns: The array of ASCII hexadecimal digits.
    public func hexEncodedBytes() -> [UInt8] {
        var result: [UInt8] = .init()
        result.reserveCapacity(self.underestimatedCount << 1) // best guess
        return self.reduce(into: result) { output, byte in
            output.append(hexTable[numericCast(byte >> 4)])
            output.append(hexTable[numericCast(byte & 0x0f)])
        }
    }
}

extension Collection where Element == UInt8 {
    
    /// Transform a `Collection` of individual bytes into an array of individual
    /// hexadecimal digits representing those bytes using ASCII codepoints,
    /// with two digits of result for each byte of input. Performance is `O(n)`
    /// and is guaranteed to only allocate once.
    ///
    /// - Returns: The array of ASCII hexadecimal digits.
    public func hexEncodedBytes() -> [UInt8] {
        return .init(unsafeUninitializedCapacity: self.count << 1) { buffer, outCount in
            for byte in self {
                (buffer[outCount + 0], buffer[outCount + 1]) = (hexTable[numericCast(byte >> 4)], hexTable[numericCast(byte & 0x0f)])
                outCount += 2
            }
        }
    }
}

extension BidirectionalCollection where Element: BinaryInteger {
    
    /// Transform a `BidirectionalCollection` of `BinaryIntegers` into a string
    /// representing the hexadecimal string representations of each of the
    /// elements of the collection, joined by commas and surrounded by array
    /// brackets. This is intended as a convenient visual representation of the
    /// contents of such a collection (such as the `words` array of an
    /// `ArbitraryInt` value), not as a canonical or lossless form. See
    /// `BinaryInteger.hexEncodedString()` for additional information.
    public func hexEncodedString() -> String {
        return "[\(self.map { $0.hexEncodedString() }.joined(separator: ", "))]"
    }
    
}
