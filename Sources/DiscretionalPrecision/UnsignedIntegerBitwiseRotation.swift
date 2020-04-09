import CDiscretionalClangBuiltins

// MARK: - `FixedWidthInteger` rotation public interface

/// These extensions define and perform a bitwise "rotate" operation. A bitwise
/// rotate functions very much like a bitwise shift, except the shifted bits are
/// "pushed" back into the value on the other end instead of a zero fill. This
/// implementation does not define rotation for signed integer values, though it
/// is possible to make such a definition, in the interest of behaving in as
/// intuitive and unambiguous asmanner as reasonably possible. Rotation is a
/// relatively common operation to desire to perform, but a surprisingly rare
/// one to find available in the core libraries of most languages. There is no
/// individual "rotate" function or operator in C, C++, Objective-C, Swift, or
/// many others, though most CPUs do provide instructions for bitwise rotation
/// at the machine language level. Just about any optimizing compiler will
/// translate the most straightforward implementation of a rotate in C-like
/// languages (the result of bitwise OR-ing a pair of inverse bit shifts) into
/// the appropriate rotate instruction in the final program, but it is
/// nonetheless sometimes desirable to explicitly express a rotation. Notably,
/// rotation can only be meaningfully defined for fixed-width values; arbitrary-
/// precision integers have no (stable) maximum width and thus can not calculate
/// the appropriate bit shifts. (One obvious workaround for this limitation is
/// to rotate such a value using its "current" width; while doing so is quite
/// straightforward, we have nonetheless chosen to not to explore it, once again
/// in the name of maintaining predictability.)
extension FixedWidthInteger where Self: UnsignedInteger {

    /// Public interface to left/counter-clockwise bitwise rotation. The input
    /// bit count may be of any `FixedWidthInteger` type; it does not need to
    /// match either `self` or `Int`. The only restriction is that that absolute
    /// value of the bit count must not exceed `Int.max`. The rotated value is
    /// returned.
    public func rotatedLeft<B: FixedWidthInteger>(by bits: B) -> Self {
        precondition(bits.magnitude <= Int.max, "May not rotate by more than Int.max bits")
        return _rotatedCommon(by: -Int(bits)) // negate to rotate left
    }

    /// Public interface to right/clockwise bitwise rotation. The input bit
    /// count may be of any `FixedWidthInteger` type; it does not need to match
    /// either `self` or `Int`. The only restriction is that that absolute value
    /// of the bit count must not exceed `Int.max`. The rotated value is
    /// returned.
    public func rotatedRight<B: FixedWidthInteger>(by bits: B) -> Self {
        precondition(bits.magnitude <= Int.max, "May not rotate by more than Int.max bits")
        return _rotatedCommon(by: Int(bits))
    }
    
    /// An in-place version of `rotatedLeft(by:)`. The algorithm used by
    /// `_rotatedCommon(by:)` can not significantly benefit from performing the
    /// rotate in-place rather than a separate result value, so the in-place
    /// variant is implemented simply by assigning the result of
    /// `rotatedLeft(by:)` to self.
    @inlinable public mutating func rotateLeft<B: FixedWidthInteger>(by bits: B) {
        self = self.rotatedLeft(by: bits)
    }
    
    /// An in-place version of `rotatedRight(by:)`. The algorithm used by
    /// `_rotatedCommon(by:)` can not significantly benefit from performing the
    /// rotate in-place rather than a separate result value, so the in-place
    /// variant is implemented simply by assigning the result of
    /// `rotatedRight(by:)` to self.
    @inlinable public mutating func rotateRight<B: FixedWidthInteger>(by bits: B) {
        self = self.rotatedRight(by: bits)
    }

}

// MARK: - `FixedWidthInteger` rotation operator definitions

/// An infix operator representing the "left rotate" operation on an input
/// operand and a bit count operand. See `<<<(_:_:)` for more details.
infix operator <<<: BitwiseShiftPrecedence

/// An infix operator representing the "right rotate" operation on an input
/// operand and a bit count operand. See `>>>(_:_:)` for more details.
infix operator >>>: BitwiseShiftPrecedence

/// An infix operator representing the "left rotate in place" operation on an
/// inout operand and a bit count operand. See `<<<=(_:_:)` for more details.
infix operator <<<=: AssignmentPrecedence

/// An infix operator representing the "right rotate in place" operation on an
/// inout operand and a bit count operand. See `>>>=(_:_:)` for more details.
infix operator >>>=: AssignmentPrecedence

/// The implementations of the above operators. Read on...
extension FixedWidthInteger where Self: UnsignedInteger {
    
    /// Performs a left rotation of `lhs` by `rhs` bits and returns the result.
    /// See `FixedWidthInteger.rotatedLeft(by:)` for all pertinent details. This
    /// operator has `BitwiseShiftPrecedence`, making it higher precedence than
    /// everything except the others in the same group, similarly to its
    /// closely related cousin operator `<<`.
    @inlinable public static func <<< <B: FixedWidthInteger>(lhs: Self, rhs: B) -> Self {
        return lhs.rotatedLeft(by: rhs)
    }
    
    /// Performs a right rotation of `lhs` by `rhs` bits and returns the result.
    /// See `FixedWidthInteger.rotatedRight(by:)` for all pertinent details.
    /// This operator has `BitwiseShiftPrecedence`, making it higher precedence
    /// than everything except the others in the same group, similarly to its
    /// closely related cousin operator `>>`.
    @inlinable public static func >>> <B: FixedWidthInteger>(lhs: Self, rhs: B) -> Self {
        return lhs.rotatedRight(by: rhs)
    }
    
    /// Performs an in-place left rotation of `lhs` by `rhs` bits. See
    /// `FixedWidthInteger.rotateLeft(by:)` for all pertinent details. This
    /// operator has `AssignmentPrecedence`, placing it near the bottom of the
    /// precedence list alongside its cousin operator `<<=`.
    @inlinable public static func <<<= <B: FixedWidthInteger>(lhs: inout Self, rhs: B) {
        lhs.rotateLeft(by: rhs)
    }
    
    /// Performs an in-place right rotation of `lhs` by `rhs` bits. See
    /// `FixedWidthInteger.rotateRight(by:)` for all pertinent details. This
    /// operator has `AssignmentPrecedence`, placing it near the bottom of the
    /// precedence list alongside its cousin operator `>>=`.
    @inlinable public static func >>>= <B: FixedWidthInteger>(lhs: inout Self, rhs: B) {
        lhs.rotateRight(by: rhs)
    }
    
}

// MARK: - `FixedWidthInteger` rotation core implementation
extension FixedWidthInteger where Self: UnsignedInteger {

    /// Perform a rotate operation on `self`, rotating by the given number of
    /// bits (modulo `Self.bitWidth`, as doing otherwise would be a potentially
    /// considerable waste of CPU time). The bit count is provided as an `Int`,
    /// under the theory that even when `Int` happens to be only 32-bit, any
    /// user who finds themselves needing to perform a rotate which exceeds 2
    /// billion bits (i.e. 2GB of memory space) is likely to need a more
    /// specialized algorithm than this in any event. If the count is greater
    /// than zero, "clockwise" rotation (to the right) is indicated. If it is
    /// less than zero, "counter-clockwise" rotation (to the left) is indicated.
    /// (In this context, we define "left" as being in the direction of the MSB
    /// and "right" as being in the directoin of the LSB, e.g. nominally "little
    /// endian".) A rotate count of zero is arguably an invalid input, but we
    /// allow it and treat it as a no-op.
    ///
    /// - Note: This algorithm attempts to leverage the availability of compiler
    ///   builtin functions for performing rotation, if the input bit count and
    ///   size of `self` are both compatible.
    ///
    /// - Note: In the case that the compiler builtins are _not_ suitable, this
    ///   algorithm next optimizes for values whose bit width is a power of two,
    ///   which is common to the overwhelming majority of fixed-width integers.
    ///   It is able to handle unusually large bit widths, such as the 512-bit
    ///   values used with AVX-512, as long as they still function as single-
    ///   precision integers (e.g. the value `self` is a singular and complete
    ///   unit, _not_ (for example) a single "digit" part of a still larger
    ///   value. In particular, the left shift `<<`, right shift `>>`, and
    ///   bitwise OR `|` operators must function correctly according to their
    ///   semantics as applied to standard integer types.
    ///
    /// - Note: In the presence of an "oddball" fixed-width value - such as one
    ///   having a unusual bit count such as 87 or 26 - the algorithm will fall
    ///   back on performing some operations using arithmetic rather than the
    ///   usually faster bitwise operators. Left and right shift, and bitwise OR
    ///   operators must still continue to function as expected, though in
    ///   particular it is _not_ required that `<<` be truncating at exactly
    ///   `Self.bitWidth`; any excess bits will be explicitly masked out.
    private func _rotatedCommon(by bits: Int) -> Self {
        guard bits != .zero else { return self } // Rotate by zero does nothing
        if bits.magnitude <= Self.max { // Attempt to delegate to the compiler builtins if the type of self is also compatible
            switch (Self.bitWidth, bits.signum()) {
            case (UInt8.bitWidth, -1): return Self(UInt8(self).rotatedRight(by: UInt8(bits.magnitude)))
            case (UInt8.bitWidth, 1): return Self(UInt8(self).rotatedLeft(by: UInt8(bits)))
            case (UInt16.bitWidth, -1): return Self(UInt16(self).rotatedRight(by: UInt16(bits.magnitude)))
            case (UInt16.bitWidth, 1): return Self(UInt16(self).rotatedLeft(by: UInt16(bits)))
            case (UInt32.bitWidth, -1): return Self(UInt32(self).rotatedRight(by: UInt32(bits.magnitude)))
            case (UInt32.bitWidth, 1): return Self(UInt32(self).rotatedLeft(by: UInt32(bits)))
            case (UInt64.bitWidth, -1): return Self(UInt64(self).rotatedRight(by: UInt64(bits.magnitude)))
            case (UInt64.bitWidth, 1): return Self(UInt64(self).rotatedLeft(by: UInt64(bits)))
            default: break
            }
        }
        // Helpfully, the standard library's bit shift operators already invert themselves when the bit count is
        // negative, and changing rotate direction is just swapping the left and right shift, so we don't have to
        // do anything special at all to make the canonical rotate expression work aside from make sure that we
        // are performing an operation in the "clockwise" or "right" direction when the bit count is positive.
        if Self.bitWidth.leadingZeroBitCount + Self.bitWidth.trailingZeroBitCount + 1 == Self.bitWidth.bitWidth {
            // If the bit width of Self has a population count of 1 (is a power of two), we can use bitwise logic,
            // as well as skip both an extra zero check and an additional masking operation which are both simply
            // a waste of CPU for this case.
            let bits = bits & (Self.bitWidth - 1) // bitwise mod to get the count into the range of the type's width
            return (self >> bits) | (self << (Self.bitWidth - bits)) // shift the bottom bits out and OR in a copy of those bits at the top
        } else {
            // For non-power-of-2 widths, we switch to slower arithmetic operations. We must check the result for
            // zero (the overhead of performing a 0-bit rotate is no longer noise in this scenario), and we also
            // have to ensure no extra bits are left behind in the upper part of the result, as a value with a bit
            // width not a power of 2 is not required to be truncating at its bit width (e.g., a 60-bit value may
            // very well implement left shift by performing it on 64-bit storage, in which case up to four bits of
            // old data are still present in that storage even though they are no longer significant to the value.
            // Normally it would be the type's own responsibility to canonicalize its storage appropriately, but in
            // the case of a rotate it is possible to end up shifting in data the type does not expect to be
            // accessed. Therefore, we perform a bitwise AND against a mask composed of exactly `Self.bitWidth` 1
            // bits; the effect is to clear any additional bits that may be present. We perform the operation again
            // a second time after the rotate, as the left-shift half of the operation may have accidentaly left
            // a copy of some or all of the rotated bits in any additional space above the official bit width.
            let bits = bits % Self.bitWidth // arithmetic mod to get the count into the range of the type's width
            guard bits != .zero else { return self } // ensure the modulo didn't produce zero
            var result = self & ((1 << Self.bitWidth) - 1) // wipe any existing overflow bits so they don't contaminate the rotate
            result = (self >> bits) | (self << (Self.bitWidth - bits)) // rotate right by the resulting bit count
            return result & ((1 << Self.bitWidth) - 1) // wipe any data we accidentally rotated into any overflow bits
        }
    }
    
}

// MARK: - `UInt8` type-specific specializations

/// Type-specific specializations of the rotation methods and operators. Refer
/// to `UInt8.rotatedLeft(by:)` for details relating to *all* specializations.
extension UInt8 {
    
    /// A specialization of `FixedWidthInteger.rotatedLeft(by:)` when the type
    /// of the bit count is the same as `Self`. In this case, we can delegate to
    /// a compiler builtin function rather than performing rotation manually.
    ///
    /// - Note: This specialization and the others on this type, and indeed the
    ///   similar specializations on the other builtin unsigned integer types,
    ///   _must_ all be provided on the concrete types to which they apply, not
    ///   generically via `FixedWidthInteger`; otherwise Swift will perform a
    ///   purely static dispatch and invoke the fully generic implementation
    ///   even when the matching type requirement is met by the concrete types.
    ///   This does lead to some unfortunate and somewhat annoying repetition.
    @inlinable public func rotatedLeft(by bits: Self) -> Self { return ClangBuiltins.rolb(x: self, y: bits) }

    /// A specialization of `FixedWidthInteger.rotatedRight(by:)` when the type
    /// of the bit count is the same as `Self`. In this case, we can delegate to
    /// a compiler builtin function rather than performing rotation manually.
    @inlinable public func rotatedRight(by bits: Self) -> Self { return ClangBuiltins.rorb(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.rotateLeft(by:)`.
    @inlinable public mutating func rotateLeft(by bits: Self) { self = ClangBuiltins.rolb(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotateRight(by:)`.
    @inlinable public mutating func rotateRight(by bits: Self) { self = ClangBuiltins.rorb(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.<<<(_:_:)`.
    @inlinable public static func <<< (lhs: Self, rhs: Self) -> Self { lhs.rotatedLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>(_:_:)`.
    @inlinable public static func >>> (lhs: Self, rhs: Self) -> Self { lhs.rotatedRight(by: rhs) }

    /// A likewise specialization of `FixedWidthInteger.<<<=(_:_:)`.
    @inlinable public static func <<<= (lhs: inout Self, rhs: Self) { lhs.rotateLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>=(_:_:)`.
    @inlinable public static func >>>= (lhs: inout Self, rhs: Self) { lhs.rotateRight(by: rhs) }
    
}

// MARK: - `UInt16` type-specific specializations

/// Type-specific specializations of the rotation methods and operators. Refer
/// to `UInt8.rotatedLeft(by:)` for details relating to *all* specializations,
/// even those on this and other unsigned integer types.
extension UInt16 {

    /// A likewise specialization of `FixedWidthInteger.rotatedLeft(by:)`.
    @inlinable public func rotatedLeft(by bits: Self) -> Self { return ClangBuiltins.rols(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotatedLeft(by:)`.
    @inlinable public func rotatedRight(by bits: Self) -> Self { return ClangBuiltins.rors(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.rotateLeft(by:)`.
    @inlinable public mutating func rotateLeft(by bits: Self) { self = ClangBuiltins.rols(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotateRight(by:)`.
    @inlinable public mutating func rotateRight(by bits: Self) { self = ClangBuiltins.rors(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.<<<(_:_:)`.
    @inlinable public static func <<< (lhs: Self, rhs: Self) -> Self { lhs.rotatedLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>(_:_:)`.
    @inlinable public static func >>> (lhs: Self, rhs: Self) -> Self { lhs.rotatedRight(by: rhs) }

    /// A likewise specialization of `FixedWidthInteger.<<<=(_:_:)`.
    @inlinable public static func <<<= (lhs: inout Self, rhs: Self) { lhs.rotateLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>=(_:_:)`.
    @inlinable public static func >>>= (lhs: inout Self, rhs: Self) { lhs.rotateRight(by: rhs) }

}

// MARK: - `UInt32` type-specific specializations

/// Type-specific specializations of the rotation methods and operators. Refer
/// to `UInt8.rotatedLeft(by:)` for details relating to *all* specializations,
/// even those on this and other unsigned integer types.
extension UInt32 {

    /// A likewise specialization of `FixedWidthInteger.rotatedLeft(by:)`.
    @inlinable public func rotatedLeft(by bits: Self) -> Self { return ClangBuiltins.rol(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotatedLeft(by:)`.
    @inlinable public func rotatedRight(by bits: Self) -> Self { return ClangBuiltins.ror(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.rotateLeft(by:)`.
    @inlinable public mutating func rotateLeft(by bits: Self) { self = ClangBuiltins.rol(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotateRight(by:)`.
    @inlinable public mutating func rotateRight(by bits: Self) { self = ClangBuiltins.ror(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.<<<(_:_:)`.
    @inlinable public static func <<< (lhs: Self, rhs: Self) -> Self { lhs.rotatedLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>(_:_:)`.
    @inlinable public static func >>> (lhs: Self, rhs: Self) -> Self { lhs.rotatedRight(by: rhs) }

    /// A likewise specialization of `FixedWidthInteger.<<<=(_:_:)`.
    @inlinable public static func <<<= (lhs: inout Self, rhs: Self) { lhs.rotateLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>=(_:_:)`.
    @inlinable public static func >>>= (lhs: inout Self, rhs: Self) { lhs.rotateRight(by: rhs) }

}

// MARK: - `UInt64` type-specific specializations

/// Type-specific specializations of the rotation methods and operators. Refer
/// to `UInt8.rotatedLeft(by:)` for details relating to *all* specializations,
/// even those on this and other unsigned integer types.
extension UInt64 {

    /// A likewise specialization of `FixedWidthInteger.rotatedLeft(by:)`.
    @inlinable public func rotatedLeft(by bits: Self) -> Self { return ClangBuiltins.rolll(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotatedLeft(by:)`.
    @inlinable public func rotatedRight(by bits: Self) -> Self { return ClangBuiltins.rorll(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.rotateLeft(by:)`.
    @inlinable public mutating func rotateLeft(by bits: Self) { self = ClangBuiltins.rolll(x: self, y: bits) }

    /// A likewise specialization of `FixedWidthInteger.rotateRight(by:)`.
    @inlinable public mutating func rotateRight(by bits: Self) { self = ClangBuiltins.rorll(x: self, y: bits) }
    
    /// A likewise specialization of `FixedWidthInteger.<<<(_:_:)`.
    @inlinable public static func <<< (lhs: Self, rhs: Self) -> Self { lhs.rotatedLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>(_:_:)`.
    @inlinable public static func >>> (lhs: Self, rhs: Self) -> Self { lhs.rotatedRight(by: rhs) }

    /// A likewise specialization of `FixedWidthInteger.<<<=(_:_:)`.
    @inlinable public static func <<<= (lhs: inout Self, rhs: Self) { lhs.rotateLeft(by: rhs) }
    
    /// A likewise specialization of `FixedWidthInteger.>>>=(_:_:)`.
    @inlinable public static func >>>= (lhs: inout Self, rhs: Self) { lhs.rotateRight(by: rhs) }

}
