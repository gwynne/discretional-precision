extension ArbitraryInt: LosslessStringConvertible {

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

}
