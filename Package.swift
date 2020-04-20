// swift-tools-version:5.2
import PackageDescription

let package = Package(
    name: "discretional-precision",
    products: [
        .library(name: "DiscretionalPrecision", targets: ["DiscretionalPrecision"]),
    ],
    dependencies: [],
    targets: [
        .target(name: "CDiscretionalClangBuiltins", dependencies: []),
        .target(name: "DiscretionalPrecision", dependencies: ["CDiscretionalClangBuiltins"]),
        .testTarget(name: "DiscretionalPrecisionTests", dependencies: ["DiscretionalPrecision"]),
        .testTarget(name: "DiscretionalPrecisionTestVectors", dependencies: ["DiscretionalPrecision"]),
        .testTarget(name: "DiscretionalPrecisionBenchmarks", dependencies: ["DiscretionalPrecision"]),
    ]
)
