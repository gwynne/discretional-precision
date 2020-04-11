/// Extend `AribtraryInt` with several "well-known" constant values. For most
/// integer types this is just a convenience for generic access, but in the
/// case of `ArbitraryInt`, an enormous speedup is realized by constructing
/// these values statically rather than letting the compiler generate
/// invocations of `.init(integerLiteral:)`.
extension ArbitraryInt {

    /// See `AdditiveArithmetic.zero`.
    ///
    /// - Note: `ArbitraryInt.init(integerLiteral: 0)` is considerably slower
    ///   than this accessor, sometimes by multiple orders of magnitude due to
    ///   the overhead of allocations.
    public static let zero: ArbitraryInt = .init(words: [0], sign: false, bitWidth: 1)
    
    /// A static accessor for `1`; this constant value is used as often as zero
    /// in various parts of `ArbitraryInt`'s implementation.
    public static let one: ArbitraryInt = .init(words: [1], sign: false, bitWidth: 1)
    
    /// A static accessor for `-1`, another constant value which is used fairly
    /// often in various parts of `ArbitraryInt`'s implementation.
    public static let minusOne: ArbitraryInt = .init(words: [1], sign: true, bitWidth: 1)
    
}

/// For the sake of feature parity and as a courtesy, we also extend
/// `BinaryInteger` to provide the `1` static constant. Because this extension
/// is inspired by an optimization of `ArbitraryInt`'s implementation and is not
/// necessarily considered to have general use in the absence of that
/// implementation, the extension is placed here instead of in its own file.
extension BinaryInteger {
    
    /// The result of applying the group 0 "successor" hyperoperation (also
    /// called such varied things as "increment", or more esoterically,
    /// "zeration") to the value of `.zero` (aka `S(0)`), as represented in the
    /// domain and radix of `Self`.
    ///
    /// - Note: There are theoretical cases where the obvious value 1 might not
    ///   be the actual result of `Self.zero.advanced(by: 1)`, such as a
    ///   supposed `NegativeInteger`, an integer designed to always have a zero
    ///   value, a domain type whose minimum was greater than `1`, an integer
    ///   representing a reversed number line, an integer in the set of only
    ///   even integers, and so forth. Most of these of these would probably not
    ///   manage to successfully conform to `BinaryInteger` anyway, though.
    public static var one: Self { 1 }

}

/// Also extend `SignedInteger` to provide the `-1` static constant. All the
/// remarks above regarding the extension for `.one` apply to this as well.
extension SignedInteger {
    
    /// The additive inverse (e.g. the result of applying the unary negation
    /// operator) of `.one`, as represented in the domain and radix of `Self`.
    ///
    /// - Note: There is no "predecessor" function in the hyperoperation
    ///   hierarchy, which essentially deals in natural numbers rather than
    ///   all integers. Still, defining `-1` as "the application of inverse
    ///   addition - e.g. subtraction - to the values `0` and `S(0)`" seemed so
    ///   excessive that even _this_ comment author, despite her obvious
    ///   predilection for delving far more deeply into mathematical background
    ///   information than almost any of the things being described actually
    ///   require, could not bring herself to offer it as the definitive
    ///   explanation...
    public static var minusOne: Self { -.one }
    
}
