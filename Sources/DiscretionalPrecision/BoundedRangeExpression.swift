/// This protocol extends `RangeExpression` by explicitly including several
/// properties and methods that are shared by both `Range` and `ClosedRange`,
/// but were not previously accessible in a generic context because they were
/// not part of any protocol (much less one that both types already shared). It
/// also makes the common `Sequence` conformance of the two types explicit. Per
/// the protocol's name, it is intended to function as a means of expressing
/// "either a `Range` or a `ClosedRange`", which `RangeExpression` can not do.
/// Conforming additional types to this protocol is not likely to be useful.
public protocol BoundedRangeExpression: RangeExpression, Sequence {
    
    /// See `Range.lowerBound` and `ClosedRange.lowerBound`.
    var lowerBound: Bound { get }

    /// See `Range.upperBound` and `ClosedRange.upperBound`.
    var upperBound: Bound { get }
    
    /// See `Range.clamped(to:)` and `ClosedRange.clamped(to:)`.
    ///
    /// - Note: This method is only available on either type when the constraint
    ///   `Bound: Comparable` is satisfied, so conforming to this protocol must
    ///   either be conditional on the same or provide an alternate
    ///   implementation for the non-`Comparable` case. This protocol chooses
    ///   not to itself require said constraint for conformance in order that
    ///   consumers of the protocol (for example, a `subscript` on a collection
    ///   type) are not necessarily required to themselves require it.
    func clamped(to limits: Self) -> Self
    
    /// Create an instance of `Self` from a `Range<Bound>`. This initializer
    /// exists on `ClosedRange` to enable quick conversion between the two. This
    /// protocol includes both it and its `ClosedRange` counterpart so as to
    /// provide a common generic interface that does not require the caller to
    /// know what type `Self` actually is. See below for more details.
    init(_ other: Range<Bound>)

    /// Create an instance of `Self` from a `ClosedRange<Bound>`. This
    /// initializer exists on `Range` to enable quick conversion between the
    /// two. This protocol includes both it and its `ClosedRange` counterpart so
    /// as to provide a common generic interface that does not require the
    /// caller to know what type `Self` actually is. See below for more details.
    init(_ other: ClosedRange<Bound>)

}

/// Conform `Range` to `BoundedRangeExpression` with sufficient conditional
/// constraints to ensure all but one of the protocol's requirements is already
/// met by functionality already available on the type.
extension Range: BoundedRangeExpression where Bound: Strideable, Bound.Stride: SignedInteger {
    
    /// `init(_:)` for `ClosedRange` is provided natively by `Range`. This
    /// initializer effectively functions as an assignment operator, but
    /// allows consumers of the protocol to write `Range.init(someRange)` or
    /// `ClosedRange.init(someRange)` without having to inspect the type of
    /// `someRange` before the fact - since this protocol has `Self`
    /// requirements, the only way to so inspect the value would be to implement
    /// the surrounding method twice, which is exactly what this protocol is
    /// intended to alleviate in the first place.
    public init(_ other: Range<Bound>) {
        self = other
    }
    
}

/// Conform `ClosedRange` to `BoundedRangeExpression` with sufficient
/// conditional constraints to ensure all but one of the protocol's requirements
/// is already met by functionality already available on the type.
extension ClosedRange: BoundedRangeExpression where Bound: Strideable, Bound.Stride: SignedInteger {

    /// `init(_:)` for `Range` is provided natively by `ClosedRange`. This
    /// initializer effectively functions as an assignment operator, but
    /// allows consumers of the protocol to write `Range.init(someRange)` or
    /// `ClosedRange.init(someRange)` without having to inspect the type of
    /// `someRange` before the fact - since this protocol has `Self`
    /// requirements, the only way to so inspect the value would be to implement
    /// the surrounding method twice, which is exactly what this protocol is
    /// intended to alleviate in the first place.
    public init(_ other: ClosedRange<Bound>) {
        self = other
    }

}
