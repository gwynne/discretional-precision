extension Array where Element == ArbitraryInt.Words.Element {
    
    public func normalized() -> Array<Element> {
        var zeroIdx = self.index(before: self.endIndex)
        while zeroIdx > self.startIndex && self[zeroIdx] == 0 { zeroIdx = self.index(before: zeroIdx) }
        if zeroIdx == self.startIndex && self[self.startIndex] == 0 { return [0] }
        return Array(self[self.startIndex...zeroIdx])
    }
    
}
