# 0023 - Packages

We want a way to have reusable units of code. I'm thinking a directory with a package.tlk file
is a package. package.tlk can look like this:

```
Package(
    name: "talk-html",
    version: "0.1.0",
    dependencies: [
        .git("https://github.com/nakajima/talk-wasm")
    ]
)
```

Here are the types I envision:

```
enum PackageArtifact {
    case lib(named: String, from: String),
    case bin(named: String, from: String)
}

enum PackageDependency {
    case git(String), tar(String)
}

struct Package {
    let name: String
    let builds: Array<PackageArtifact>
    let version: String
    let dependencies: Array<PackageDependency>
}
```

## Structure

```
talk-html/
|- package.tlk
|- src/
  |- bin/
    |- talkhtml.tlk     # anything under bin/ is compiled as a binary
  |- lib.tlk            # if lib.tlk is present, anything it exports will be importable as the lib
|- test/
|- buildin/
  |- packages/
```

When a package.tlk is present, the package.tlk's sibling src/ directory should be considered the entirely workspace for the compiler (plus dependencies).
