/// Extend `AribtraryInt` with several "well-known" constant values. For most
/// integer types this is just a convenience for generic access, but in the
/// case of `ArbitraryInt`, an enormous speedup is realized by constructing
/// these values statically rather than letting the compiler generate
/// invocations of `.init(integerLiteral:)`. We also define some useful values
/// for internal use, mostly short names for common bitwise calculations.
extension ArbitraryInt {

    /// See `AdditiveArithmetic.zero`.
    ///
    /// - Note: `ArbitraryInt.init(integerLiteral: 0)` is considerably slower
    ///   than this accessor, sometimes by multiple orders of magnitude due to
    ///   the overhead of allocations.
    public static let zero: ArbitraryInt = .init(storage: [0], sign: false)
    
    /// A static accessor for `1`; this constant value is used as often as zero
    /// in various parts of `ArbitraryInt`'s implementation.
    public static let one: ArbitraryInt = .init(storage: [1], sign: false)
    
    /// A static accessor for `-1`, another constant value which is used fairly
    /// often in various parts of `ArbitraryInt`'s implementation.
    public static let minusOne: ArbitraryInt = .init(storage: [1], sign: true)
    
    /// The radix `𝑟` of our digits, i.e. the exact number of unique values it
    /// is possible for one digit to represent. This value is often referred to
    /// as the base `𝑏`; `𝑏` and `𝑟` both refer to the same concept and value and
    /// are interchangeable unless otherwise specified in a particular context.
    /// While an integer type may theoretically chooes any internal
    /// representation of its values, in practice it is all but universal to use
    /// a fixed-radix numeral system. Equally as common is the use of base `2`
    /// or an integral power of `2`, since non-power-of-two representations tend
    /// to necessitate computationally expensive conversions on a prohibitively
    /// frequent basis. Mathematically, the radix is a value which is typically
    /// specified contextually, rather than being derived. However, if a closely
    /// related value is available, such as the number of digits `𝓃` necessary
    /// to express the radix itself in an unambiguous base like binary, it can
    /// then be derived as simply `2ⁿ`. And, of course, given that `𝓃` is a
    /// count of bits, the value can be more efficiently computed as `1 << 𝓃`.
    /// In our specific case, it is much easier to start from the bit count of
    /// the type we use in our internal representation and compute from there.
    /// Because our internal representation uses the largest of the builtin
    /// integer types, the `radix` value naturally exceeds the maximum value of
    /// that type by exactly one. There being no builtin type which can
    /// represent the value, `radix` is stored as an instance of `Self`.
    ///
    /// - Note: (What, more notes?) A typical radix for any given integer
    ///   representation tends to be a small number - 16 for hexadecimal, 10 for
    ///   decimal, 8 for octal, 2 for binary, etc. However, as an arbitrary-
    ///   precision type, `ArbitraryInt` is designed to deal with extremely
    ///   large numbers as efficiently as possible. One of the consequences of
    ///   this design is a desire to define the single-precision operations used
    ///   by many multiple-precision algorithms such that they operate on as
    ///   large a portion of an arbitrary-precision value as possible with each
    ///   invocation. The smallest "unit" of operation for most algorithms is a
    ///   single "digit" in a given base, so we have defined our radix such that
    ///   one arbitrary-precision digit holds exactly one machine word's worth
    ///   of possible values, or in other words, we have chosen to use a machine
    ///   word _as_ our digit. Our `radix` is therefore the maximum value of a
    ///   machine word plus one, and the bit width of that radix is, naturally,
    ///   that of the machine word. One interesting consequence to this choice
    ///   of definition - and of not hardcoding it to be any specific exact bit
    ///   width - is that the definition of single-precision operations and the
    ///   corresponding efficiency characteristics will vary between the bitness
    ///   of the underlying operating systems and CPUs on which this code runs.
    ///   In other words, we will use 32-bit operations on 32-bit machines and
    ///   64-bit operations on 64-bit machines, and 128-bit operations on a
    ///   hypothetical 128-bit machine, and even 16- or 8-bit operations on such
    ///   CPUs, presuming one could first induce Swift to execute thereupon.
    ///
    /// - Note: Notably, the previous characteristic re: bitness-adaptivity has
    ///   little or no effect on vectorization, which we make no attempt
    ///   whatsoever to leverage at the time of this writing, beyond whatever
    ///   the compiler might auto-vectorize on its own, and would likely see
    ///   some interesting (and potentially difficult) behaviors emerge when
    ///   dealing with SIMD.
    @usableFromInline internal static var radix: ArbitraryInt = .one << Self.radixBitWidth
 
    /// The number of base-2 digits (bits) needed to fully express a single
    /// digit as represented in our internal storage using radix `𝑟`.
    /// Mathematically, this value is expressed by `ceil(log₂(𝑟))`; however, the
    /// requirement that `𝑟` be a power of 2 allows defining it as simply the
    /// bit width of the type used to represent an individual digit. See `radix`
    /// above for copious additional specifics.
    @usableFromInline internal static var radixBitWidth: Int = Words.Element.bitWidth
    
    /// The number of bits by which a value must be shifted to multiply or
    /// divide it by the `radixBitWidth`, which is also equivalent to adding or
    /// subtracting the `radix`. This is mathematically `ceil(log₂(𝑤))`, given
    /// `𝑤` as the `radixBitWidth` value. It could also be calculated from the
    /// radix by using the definition of `𝑤` as `ceil(log₂(𝑟))`, yielding
    /// `ceil(log₂(ceil(log₂(𝑟))))` - a sufficiently annoying-looking expression
    /// that just using the width (on which the radix is based in fact anyhow)
    /// is the obviously superior option.
    @usableFromInline internal static var radixBitShift: Int = Self.radixBitWidth.trailingZeroBitCount
    
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
