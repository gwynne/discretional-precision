import CDiscretionalClangBuiltins

// MARK: - `FixedWidthInteger` multiprecision arithmetic public interface

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
    
    /// Perform a "full-width" addition, as it were, returning the result of
    /// adding two single-precision values as a pair of the single-precision
    /// result and the one-bit carry/overflow flag, which can be conveniently
    /// conceptualized as a second single-precision value carrying additional
    /// bits of result. The behavior and convention match one-to-one with the
    /// semantics of the standard library's `multipliedFullWidth(ny:)` method,
    /// save that the "high" word of the result will always be exactly zero or
    /// exactly one. As with that method, this one can be chained to add values
    /// of arbitrary precision by adding the high word of the result to the next
    /// word of input, ad infinitum.
    public func addedPreservingCarry(to other: Self, carryin: Self = Self.zero) -> (carry: Self, sum: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: false) as (Self, Self.Magnitude)
    }
    
    /// Perform a single step in a mutiple-precision subtraction chain,
    /// maintaining a carry bit. The carry better known when working with
    /// subtraction as a _borrow_, but as far as the CPU and logic are
    /// concerned, it's the same thing. This method uses the same verbiage of
    /// "preserving a carry" as `addedPreservingCarry(to:carryin:)`, as seen
    /// above. This was chosen specifically to match the standard library's
    /// apparent conventions for naming special arithmetic operations - the
    /// `multipliedFullWidth(by:)` method (the counterpart to multiprecision
    /// addition) uses past tense, while `dividingFullWidth(_:)`, subtraction's
    /// counterpart, uses present tense and reverse operand order (one calls the
    /// method on the divisor, not the dividend). It's notable that addition and
    /// multiplication are also both commutative, so parameter order is
    /// irrelevant, which is not true of the other two. In any case, our
    /// addition method likewise speaks of past tense, so here the subtraction
    /// method uses present tense, is invoked on the subtrahend, and is provided
    /// the minuend as a parameter, the inverse of how the subtraction would be
    /// written on paper. Naturally, we do our best to match the overall
    /// semantics of `dividingFullWidth(_:)` while also exposing the behavioral
    /// semantics of the underlying `subc` builtins in a manner which is
    /// appropriately symmetrical with the `addc` builtins. As with the addition
    /// method, this method can be chained as many times as needed to perform
    /// more or less `O(n)` subtraction on integers of arbitrary precision, as
    /// long as those integers represent individual digits in a single-precision
    /// form. Also as with addition, if the final subtraction step reseults in
    /// a nonzero carry, the extra bit of result must be accounted for. In
    /// subtraction's case it means the full-precision difference is negative
    /// (i.e. the subtrahend was larger than the minuend). This method and its
    /// constituents have no responsibility for handling that, and no ability
    /// to do so either; they deal only in unsigned values modulo their radix.
    public func subtractingPreservingCarry(from other: Self, carryin: Self = Self.zero) -> (carry: Self, difference: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: true) as (Self, Self.Magnitude)
    }
}

// MARK: - `UInt8` type-specific specializations (PUBLIC)

/// Public type-specific specializations of the multi-precision arithmetic
/// methods. Refer to the extensions on `UInt8` for detailed descriptions
/// relevant to the specializations for *all* types.
extension UInt8 {

    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.addedPreservingCarry(to:carrying:)` (see above) in
    /// all respects, except that the type of `Self` is concretely known.
    public func addedPreservingCarry(to other: Self, carryin: Self = Self.zero) -> (carry: Self, sum: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: false) as (Self, Self.Magnitude)
    }
    
    /// Type-specific implementation. Has exactly the same semantics as
    /// `FixedWidthInteger.subtractingPreservingCarry(to:carrying:)` (see above)
    /// in all respects, except that the type of `Self` is concretely known.
    public func subtractingPreservingCarry(from other: Self, carryin: Self = Self.zero) -> (carry: Self, difference: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: true) as (Self, Self.Magnitude)
    }

}

// MARK: - `UInt16` type-specific specializations (PUBLIC)

/// Public type-specific specializations of the multi-precision arithmetic
/// methods. Refer to the extensions on `UInt8` for detailed descriptions
/// relevant to the specializations for *all* types.
extension UInt16 {

    /// See `UInt8.addedPreservingCarry(to:carryin:)`
    public func addedPreservingCarry(to other: Self, carryin: Self = Self.zero) -> (carry: Self, sum: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: false) as (Self, Self.Magnitude)
    }
    
    /// See `UInt8.subtractingPreservingCarry(from:carryin:)`
    public func subtractingPreservingCarry(from other: Self, carryin: Self = Self.zero) -> (carry: Self, difference: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: true) as (Self, Self.Magnitude)
    }

}

// MARK: - `UInt32` type-specific specializations (PUBLIC)

/// Public type-specific specializations of the multi-precision arithmetic
/// methods. Refer to the extensions on `UInt8` for detailed descriptions
/// relevant to the specializations for *all* types.
extension UInt32 {

    /// See `UInt8.addedPreservingCarry(to:carryin:)`
    public func addedPreservingCarry(to other: Self, carryin: Self = Self.zero) -> (carry: Self, sum: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: false) as (Self, Self.Magnitude)
    }
    
    /// See `UInt8.subtractingPreservingCarry(from:carryin:)`
    public func subtractingPreservingCarry(from other: Self, carryin: Self = Self.zero) -> (carry: Self, difference: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: true) as (Self, Self.Magnitude)
    }

}

// MARK: - `UInt64` type-specific specializations (PUBLIC)

/// Public type-specific specializations of the multi-precision arithmetic
/// methods. Refer to the extensions on `UInt8` for detailed descriptions
/// relevant to the specializations for *all* types.
extension UInt64 {

    /// See `UInt8.addedPreservingCarry(to:carryin:)`
    public func addedPreservingCarry(to other: Self, carryin: Self = Self.zero) -> (carry: Self, sum: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: false) as (Self, Self.Magnitude)
    }
    
    /// See `UInt8.subtractingPreservingCarry(from:carryin:)`
    public func subtractingPreservingCarry(from other: Self, carryin: Self = Self.zero) -> (carry: Self, difference: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: true) as (Self, Self.Magnitude)
    }
    
}

// MARK: - `UInt` type-specific specializations (PUBLIC)

/// Public type-specific specializations of the multi-precision arithmetic
/// methods. Refer to the extensions on `UInt8` for detailed descriptions
/// relevant to the specializations for *all* types.
extension UInt {

    /// See `UInt8.addedPreservingCarry(to:carryin:)`
    public func addedPreservingCarry(to other: Self, carryin: Self = Self.zero) -> (carry: Self, sum: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: false) as (Self, Self.Magnitude)
    }
    
    /// See `UInt8.subtractingPreservingCarry(from:carryin:)`
    public func subtractingPreservingCarry(from other: Self, carryin: Self = Self.zero) -> (carry: Self, difference: Self.Magnitude) {
        return Self._arithmeticPreservingCarry(a: self, b: other, carryin: carryin, isNow: true) as (Self, Self.Magnitude)
    }
    
}

// MARK: - `FixedWidthInteger` multiprecision arithmetic core implementation

extension FixedWidthInteger where Self: UnsignedInteger {

    /// As it turns out, the implementations for carry-preserving addition and
    /// carry-preserving subtraction are pretty much identical, except for an
    /// "A or B" choice of method to call and the order of the two inputs.
    /// So, as was done with the left and right bitwise rotation logic over in
    /// that file (go look, it's not hard to find), use a single common
    /// implementation that knows to do one or the other in the two places total
    /// it matters in the slightest. Unlike the rotate, though, since one of the
    /// two inputs is `self`, we made this common method static so it can take
    /// both inputs as parameters. Most of our variants (as opposed to
    /// invariants, see?) come from `Self`, not `self`, anyway.
    ///
    /// - Note: The `isNow` parameter, which would probably have been better, if
    ///   quite verbosely, named `whateverIsHappeningNowIsHappeningNow`, is the
    ///   only discriminator needed to decide between addition and subtraction.
    ///   (Hint: Look at the verb tenses of the public method names.)
    private static func _arithmeticPreservingCarry(a: Self, b: Self, carryin: Self, isNow: Bool) -> (carry: Self, result: Self.Magnitude) {
        precondition(Self.Magnitude.bitWidth >= Self.bitWidth, "\(Self.self) needs a larger Magnitude than \(Self.Magnitude.self)")
        
        // Attempt to delegate directly to a compiler builtin via a compatible builtin type.
        switch (Self.Magnitude.bitWidth, Self.bitWidth) {
        case (UInt8.Magnitude.bitWidth,  UInt8.bitWidth...):  return UInt8._arithmeticPreservingCarryConverting(a: a, b: b, carryin: carryin, isNow: isNow)
        case (UInt16.Magnitude.bitWidth, UInt16.bitWidth...): return UInt16._arithmeticPreservingCarryConverting(a: a, b: b, carryin: carryin, isNow: isNow)
        case (UInt32.Magnitude.bitWidth, UInt32.bitWidth...): return UInt32._arithmeticPreservingCarryConverting(a: a, b: b, carryin: carryin, isNow: isNow)
        case (UInt64.Magnitude.bitWidth, UInt64.bitWidth...): return UInt64._arithmeticPreservingCarryConverting(a: a, b: b, carryin: carryin, isNow: isNow)
        default: break
        }
        
        // Okay, so none of the builtins we can use can handle `Self`, it's either too wide or has a weird bit width (like
        // `UInt56`). Reduce it by repeatedly running the arithmetic operation over its component words and let `UInt` do
        // the work. Too-small types effectively upconvert to `UInt` immediately and just need a quick adjustment by bit shift.
        // Bit widths not divisible by 8 are hereby warned that their left bitshift, right bitshift, and bitwise OR operators
        // had better work correctly and perform appropriate masking etc., otherwise the results are unpredictable. Also, because
        // we use `words` array to get at the value generically, we much guarantee that the full bit width of the type is
        // represented therein - i.e. that the collection is zero-padded on the right up to the type's bit width. This is important
        // enough that we declare it an invariant we can't function in the absence of.
        precondition(a.words.count == b.words.count && a.words.count * Self.Magnitude.Words.Element.bitWidth >= Self.bitWidth, """
            \(Self.self) must have a words array whose total bit width is at least its own Magnitude's, but
            \(a.words.count * Self.Magnitude.Words.Element.bitWidth) < \(Self.bitWidth).
            """)
        
        // Set up to iterate both word arrays and track the results as a single value of type `Self` plus carry bit.
        var aWords = a.words.makeIterator(), bWords = b.words.makeIterator(), aWord = aWords.next(), bWord = bWords.next()
        var result: Self.Magnitude = .zero, resultWord = Self.Magnitude.Words.Element.zero, carryWord = Self.Words.Element.zero
        
        // Loop while either or both values have unprocessed words, but stop after one loop if the type is smaller than one word.
        repeat {
            (carryWord, resultWord) = Self.Words.Element._arithmeticPreservingCarry(a: aWord ?? .zero, b: bWord ?? .zero, carryin: carryWord, isNow: isNow)

            // Push the latest result word into the highest word of the overall result. The generic way to do this without baking
            // a hard dependency on the number of total words into the logic is to OR it into the _lowest_ word (which is guaranteed
            // to be zero), and rotate right by the smaller of the word's bit width or the type's bit width.
            result = (result | .init(resultWord)) >>> Swift.min(resultWord.bitWidth, Self.bitWidth)

            (aWord, bWord) = (aWords.next(), bWords.next())
        } while aWord ?? bWord != nil && Self.bitWidth > resultWord.bitWidth

        // Make sure the result value is aligned to the LSB by right-shifting it by the difference between the word and type widths.
        result >>= Swift.max(resultWord.bitWidth - Self.bitWidth, 0)
        
        return (carry: Self(carryWord), result: result)
    }

}

// MARK: - `UInt8` type-specific specializations (private)

/// Type-specific specializations of the multi-precision arithmetic private
/// implementation methods. Refer to the extensions on `UInt8` for detailed
/// descriptions relevant to the specializations for *all* types. In particular,
/// `UInt8._arithmeticPreservingCarry(a:b:carryin:isNow:)` is the core method of
/// the entire implementation, being - along with its dopplegangers on the other
/// builtin types - the only methods that actually invoke the compiler builtins
/// to perform the arithmetic operations and thus the only reason any math
/// actually gets executed at all.
extension UInt8 {

    /// Type-specific implementation of
    /// `FixedWidthInteger._arithmeticPreservingCarry(a:b:carryin:isNow:)`. This
    /// is the method that actually invokes the builtins (finally). Same
    /// semantics as the generic version, but knowing the concrete type REALLY
    /// cuts down on the amount of effort needed.
    fileprivate static func _arithmeticPreservingCarry(a: Self, b: Self, carryin: Self, isNow: Bool) -> (carry: Self, result: Self.Magnitude) {
        var carryout = Self.zero
        let result = (isNow ? ClangBuiltins.subcb : ClangBuiltins.addcb)(isNow ? b : a, isNow ? a : b, carryin, &carryout)
        return (carry: carryout, result: result)
    }

    /// Utility method. Accepts an arbitrary unsigned `FixedWidthInteger` type
    /// which is guaranteed by the caller to have `T.bitWidth >= Self.bitWidth`
    /// and `T.Magnitude.bitWidth == Self.Magnitude.bitWdith`. With those
    /// guarantees, it is safe (enough) to cast the inputs to `Self` (via the
    /// non-throwing nin-optional initializer) and cast the results back to `T`.
    /// We have to put this method here rather than on `FixedWidthInteger`
    /// because Swift will not dispatch to specialized overrides of a method not
    /// declared on the original protocol (which we don't control).
    fileprivate static func _arithmeticPreservingCarryConverting<T>(a: T, b: T, carryin: T, isNow: Bool) -> (carry: T, result: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self._arithmeticPreservingCarry(a: Self.init(a), b: Self.init(b), carryin: Self.init(carryin), isNow: isNow)
        return (carry: T.init(selfCarryout), result: T.Magnitude.init(selfResult))
    }
    
}

// MARK: - `UInt16` type-specific specializations (private)

/// Type-specific specializations of the multi-precision arithmetic private
/// implementation methods. Refer to the extensions on `UInt8` for detailed
/// descriptions relevant to the specializations for *all* types.
extension UInt16 {

    /// See` UInt8._arithmeticPreservingCarry(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarry(a: Self, b: Self, carryin: Self, isNow: Bool) -> (carry: Self, result: Self.Magnitude) {
        var carryout = Self.zero
        let result = (isNow ? ClangBuiltins.subcs : ClangBuiltins.addcs)(isNow ? b : a, isNow ? a : b, carryin, &carryout)
        return (carry: carryout, result: result)
    }

    /// See `UInt8._arithmeticPreservingCarryConverting(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarryConverting<T>(a: T, b: T, carryin: T, isNow: Bool) -> (carry: T, result: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self._arithmeticPreservingCarry(a: Self.init(a), b: Self.init(b), carryin: Self.init(carryin), isNow: isNow)
        return (carry: T.init(selfCarryout), result: T.Magnitude.init(selfResult))
    }

}

// MARK: - `UInt32` type-specific specializations (private)

/// Type-specific specializations of the multi-precision arithmetic private
/// implementation methods. Refer to the extensions on `UInt8` for detailed
/// descriptions relevant to the specializations for *all* types.
extension UInt32 {

    /// See` UInt8._arithmeticPreservingCarry(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarry(a: Self, b: Self, carryin: Self, isNow: Bool) -> (carry: Self, result: Self.Magnitude) {
        var carryout = Self.zero
        let result = (isNow ? ClangBuiltins.subc : ClangBuiltins.addc)(isNow ? b : a, isNow ? a : b, carryin, &carryout)
        return (carry: carryout, result: result)
    }

    /// See `UInt8._arithmeticPreservingCarryConverting(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarryConverting<T>(a: T, b: T, carryin: T, isNow: Bool) -> (carry: T, result: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self._arithmeticPreservingCarry(a: Self.init(a), b: Self.init(b), carryin: Self.init(carryin), isNow: isNow)
        return (carry: T.init(selfCarryout), result: T.Magnitude.init(selfResult))
    }

}

// MARK: - `UInt64` type-specific specializations (private)

/// Type-specific specializations of the multi-precision arithmetic private
/// implementation methods. Refer to the extensions on `UInt8` for detailed
/// descriptions relevant to the specializations for *all* types.
extension UInt64 {

    /// See` UInt8._arithmeticPreservingCarry(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarry(a: Self, b: Self, carryin: Self, isNow: Bool) -> (carry: Self, result: Self.Magnitude) {
        var carryout = Self.zero
        let result = (isNow ? ClangBuiltins.subcll : ClangBuiltins.addcll)(isNow ? b : a, isNow ? a : b, carryin, &carryout)
        return (carry: carryout, result: result)
    }

    /// See `UInt8._arithmeticPreservingCarryConverting(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarryConverting<T>(a: T, b: T, carryin: T, isNow: Bool) -> (carry: T, result: T.Magnitude)
        where T: FixedWidthInteger, T: UnsignedInteger
    {
        assert(T.bitWidth >= Self.bitWidth && T.Magnitude.bitWidth == Self.Magnitude.bitWidth, "Caller did not ensure bit width!")
        let (selfCarryout, selfResult) = Self._arithmeticPreservingCarry(a: Self.init(a), b: Self.init(b), carryin: Self.init(carryin), isNow: isNow)
        return (carry: T.init(selfCarryout), result: T.Magnitude.init(selfResult))
    }

}

// MARK: - `UInt` type-specific specializations (private)

/// Type-specific specializations of the multi-precision arithmetic private
/// implementation methods. Refer to the extensions on `UInt8` for detailed
/// descriptions relevant to the specializations for *all* types.
extension UInt {

    /// See` UInt8._arithmeticPreservingCarry(a:b:carryin:isNow:)`
    fileprivate static func _arithmeticPreservingCarry(a: Self, b: Self, carryin: Self, isNow: Bool) -> (carry: Self, result: Self.Magnitude) {
        var carryout = Self.zero
        let result = (isNow ? ClangBuiltins.subcl : ClangBuiltins.addcl)(isNow ? b : a, isNow ? a : b, carryin, &carryout)
        return (carry: carryout, result: result)
    }

}

