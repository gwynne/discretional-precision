extension ArbitraryInt {

    /// `Storage` is the underlying storage type which backs `ArbitraryInt`.
    /// Conceptually, it is a mutable, ordered, contiguous, random-access
    /// collection of base 2**64 digits, stored in little-endian order,
    /// preserving the invariant that there must always be at least one digit,
    /// that the most significant digit may not be zero unless it is the only
    /// digit, and that the value of zero precludes the owning integer's sign
    /// flag from being set.
    ///
    /// Right now, in practice, it's as thin a wrapper as possible for `Array`.
    /// The only reason it's not just a flat-out `typealias` is to make it
    /// easier to change the implementation later if it's found that doing so
    /// would be beneficial. Also to avoid polluting `Array`'s namespace.
    ///
    /// This is a MASSIVE list of inlinable forwarders. Hopefully the compiler
    /// gets the idea...
    @usableFromInline internal struct Storage:
        CustomStringConvertible, CustomDebugStringConvertible, Equatable, Hashable, Codable, CustomReflectable
    {
        /// Underlying storage, the actual place the data lives.
        @usableFromInline internal var base: [UInt]
        
        /// Designated initializer
        @inlinable public init(base: [UInt]) { self.base = base }
        
        // Everything from here on down is a forwarder to `base`'s implementation.
        
        public typealias Element = UInt
        public typealias Index = Array<Element>.Index
        public typealias SubSequence = Array<Element>.SubSequence
        
        @inlinable public var isEmpty: Bool { base.isEmpty }
        @inlinable public var count: Int { base.count }
        @inlinable public var startIndex: Int { base.startIndex }
        @inlinable public var endIndex: Int { base.endIndex }
        @inlinable public var first: Element? { base.first }
        @inlinable public var last: Element? { base.last }

        public init(from decoder: Decoder) throws { self.init(base: try Array<Element>.init(from: decoder)) }
        public func encode(to encoder: Encoder) throws { try base.encode(to: encoder) }
        public var customMirror: Mirror { base.customMirror }
        public var description: String { base.description }
        public var debugDescription: String { base.debugDescription }
        @inlinable public static func != (lhs: Storage, rhs: Storage) -> Bool { lhs.base != rhs.base }
        @inlinable public static func == (lhs: Storage, rhs: Storage) -> Bool { lhs.base == rhs.base }
        @inlinable public func hash(into hasher: inout Hasher) { base.hash(into: &hasher) }

        @inlinable public init(repeating repeatedValue: Element, count: Int) { self.init(base: .init(repeating: repeatedValue, count: count)) }
        @inlinable public init<S>(_ elements: S) where S : Sequence, Self.Element == S.Element { self.init(base: .init(elements)) }

        @inlinable public func firstIndex(where predicate: (Element) throws -> Bool) rethrows -> Int? { try base.firstIndex(where: predicate) }
        @inlinable public func lastIndex(where predicate: (Element) throws -> Bool) rethrows -> Int? { try base.lastIndex(where: predicate) }

        @inlinable public func map<T>(_ transform: (Element) throws -> T) rethrows -> [T] { try base.map(transform) }
        @inlinable public func reversed() -> ReversedCollection<Array<Element>> { base.reversed() }

        @inlinable public subscript(index: Int) -> Element { get { base[index] } set { base[index] = newValue } }
        @inlinable public subscript(bounds: Range<Int>) -> SubSequence { get { base[bounds] } set { base[bounds] = newValue } }

        @inlinable public mutating func append(_ newElement: Element) { base.append(newElement) }
        @inlinable public mutating func append<S>(contentsOf newElements: S) where S : Sequence, Self.Element == S.Element { base.append(contentsOf: newElements) }
        @inlinable public mutating func insert(_ newElement: Element, at i: Int) { base.insert(newElement, at: i) }
        @inlinable public mutating func insert<C>(contentsOf newElements: C, at i: Int) where C : Collection, Self.Element == C.Element { base.insert(contentsOf: newElements, at: i) }
        @inlinable public mutating func removeFirst(_ k: Int) { base.removeFirst(k) }
        @inlinable public mutating func removeFirst() -> Element { base.removeFirst() }
        @inlinable public mutating func removeLast() -> Element { base.removeLast() }
        @inlinable public mutating func removeLast(_ k: Int) { base.removeLast(k) }

        // Things that don't get used on `Storage` but probably should be.
        @inlinable public var lazy: LazySequence<Array<Element>> { base.lazy }
        @inlinable public mutating func reserveCapacity(_ n: Int) { base.reserveCapacity(n) }
    }
    
    /// Simple forwarding initializer so a bunch of call sites that pass in an
    /// array directly don't have to explicitly init Storage.
    @usableFromInline internal init(storage: Array<Storage.Element>, sign: Bool) {
        self.init(storage: Storage(base: storage), sign: sign)
    }
    
    /// Input-normalizing initializer. Trims trailing zero values from the end
    /// of the input array of digits before sending them on to become the
    /// backing of a new value.
    @usableFromInline internal init(normalizing digits: Array<Storage.Element>, sign: Bool) {
        var digits = digits
        while digits.last == 0 { _ = digits.removeLast() }
        if digits.isEmpty { digits = [0] }
        self.init(storage: Storage(base: digits), sign: sign)
    }

}

extension ArbitraryInt.Storage {
    
    /// True if the storage contains a value representing zero, aka `== .zero`.
    @inlinable public var isZeroRepresentation: Bool {
        self.count == 1 && self.first == 0
    }
    
    /// Quick reimplementation of the version of this on
    /// `BidirectionalCollection`, since `Storage` deliberately does not conform
    /// to the collection protocols.
    public func hexEncodedString() -> String {
        return "[\(self.map { $0.hexEncodedString() }.joined(separator: ", "))]"
    }

}
