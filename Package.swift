// swift-tools-version:5.2
import PackageDescription

let package = Package(
    name: "DiscretionalPrecision",
    products: [
        .library(name: "DiscretionalPrecision", targets: ["DiscretionalPrecision"]),
    ],
    dependencies: [],
    targets: [
        .target(name: "DiscretionalPrecision", dependencies: []),
        .testTarget(name: "DiscretionalPrecisionTests", dependencies: ["DiscretionalPrecision"]),
        .testTarget(name: "DiscretionalPrecisionTestVectors", dependencies: ["DiscretionalPrecision"]),
        .testTarget(name: "DiscretionalPrecisionBenchmarks", dependencies: ["DiscretionalPrecision"]),
    ]
)
