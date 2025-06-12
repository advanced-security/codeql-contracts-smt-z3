# SMT constraint solving in CodeQL with Z3

Queries and infrastructure to discover C++ contract violations using the Z3 SMT solver, and support
for custom CodeQL queries that may wish use the Z3 solver API.

This repository is the home for the following CodeQL packs and plugins:

- `advanced-security/z3-cpp`: A CodeQL pack for discovering possible C++ contract violations in C++
   code using Z3 via the `advanced-security/z3` pack and `z3-plugin.jar` plugin.
- `advanced-security/z3`: A CodeQL pack for calling the Z3 solver API via a CodeQL plugin.
- `z3-plugin.jar` / `com.github.codeql.z3.Z3Plugin`: A CodeQL plugin for calling the Z3 solver API directly from CodeQL queries.

**NOTICE: This package will not be functional at first when installed as a CodeQL pack, and requires a follow-up CodeQL plugin installation step and a local installation of Z3 lib. See instructions below.**

## Background

The primary focus of this project is to validate a reasonable subset of C++ contracts specified
with assertions, and to support [C++26](https://en.cppreference.com/w/cpp/language/contracts.html)
as these first class contracts are supported by compilers.

This project also serves as a useful example that may benefit other languages, and the availability
of Z3 inside CodeQL queries may have other useful applications that may deserve to be integrated
into this project in the future.

## License

This project is licensed under the terms of the MIT open source license. Please refer to [MIT](./LICENSE.txt) for the full terms.

CodeQL is subject to the [GitHub CodeQL Terms & Conditions](https://securitylab.github.com/tools/codeql/license).

## Requirements

Running the queries from this project requires:

- macOS, Windows, Linux, or other systems compatible with both CodeQL and libZ3
- Local installation of the CodeQL CLI, and a license to use CodeQL on your project (it is free for
   open source)
- A [CodeQL database for your project](https://docs.github.com/en/code-security/codeql-cli/getting-started-with-the-codeql-cli/preparing-your-code-for-codeql-analysis)
- Local installation of the Z3 SMT solver library including java bindings (best effort instructions
   are provided below, some systems may have different installation requirements)
- Local installation of the `z3-plugin.jar` CodeQL plugin (best effort instructions are provided
   below, some systems may have different installation requirements)
- Local installation of the `z3-cpp` CodeQL pack (instructions below).

## Use + Installation

### Install Z3 lib

Firstly, make sure **Z3 is installed** on your system.

#### macOS

Download the matching Z3 release artifacts from GitHub and install them as follows:

```sh
ln -s /path/to/z3/libz3.dylib /usr/local/lib
ln -s /path/to/z3/libz3java.dylib $HOME/Library/Java/Extensions
```

**Important**: You may have to do the following as well, due to loading issues on Mac OS X.

```sh
install_name_tool -change libz3.dylib @loader_path/libz3.dylib $HOME/Library/Java/Extensions/libz3java.dylib
```

#### Linux

If possible, install `libz3java` via your package manager. Otherwise, download the Z3 release artifacts from their GitHub page.

```sh
sudo yum install z3-java # RHEL example
```

You may have to find `libz3java.so` (for instance, `/usr/lib64/z3/libz3java.so`) and symlink it to a standard `java.library.path` intended for user customization (for instance, `/usr/java/packages/lib`).

```sh
sudo mkdir -p /usr/java/packages # if it doesn't already exist
sudo ln -s /usr/lib/z3/libz3java.so /usr/java/packages/lib
```

#### Using Package Managers

Prebuilt Z3 library packages are available on brew, chocolatey, and most Linux package managers, however they do not all ship with Java bindings.

```sh
# macOS: NOT compatible (no java bindings)
brew install z3

# Windows (unknown compatibility)
choco install z3

# RHEL linux (partial compatibility)
sudo yum install java-z3

# example other linux (unknown compatibility)
sudo apt install z3
```

The Z3 project also has prebuilt binaries available for download on GitHub and instructions for building from source.

### Add the latest z3-plugin.jar to codeql

Download the latest `z3-plugin.jar` release from this project and place it in `$CODEQL_HOME/tools/z3-plugin.jar`, in the same directory as `codeql.jar`.

### Add package depenency

In `qlpack.yml` ensure the following dependencies exist:

```yaml
dependencies:
  advanced-security/z3: "*" # Use this dependency if you want to access the Z3 solver API directly
  # ... OR ...
  advanced-security/z3-cpp: "*" # Use this dependency if you want the Z3 solver with cpp analysis integration
```

and run `codeql pack install` from the command line, or run "**CodeQL install pack dependencies**" from VSCode.

### Import

In your CodeQL package, you can now import the z3 libs, and/or the z3-cpp libs.

#### Z3 only

```ql
import z3.Z3

from string spec
where spec =
  "(declare-const x Int)\n" +
  "(declare-const y Int)\n" +
  "(assert (= x y))\n" +
  "(check-sat)\n" +
  "(get-model)\n"
select Z3::getModel(spec)
```

#### Z3-cpp integrations

```ql
import cpp
import z3.cpp.Translation

from Expr e
select exprToZ3(e)
```

### (Optional) Suppress CodeQL Experimental Warning

When compiling queries that use the Z3 plugin, CodeQL will issue a warning:

```log
Warning: `invokePlugin` is part of the experimental 'plugin' feature.
```

To suppress this on the command line, use the flag `--allow-experimental=plugin`.

## Debugging Installation

Installation issues may arise using this plugin. Here are some steps to narrow down where the issue may lie.

### Confirm `z3-plugin.jar` / libz3 compatibility

Run the following test entry point in the `z3-plugin.jar`.

```sh
java -jar /path/to/z3-plugin.jar com.github.codeql.z3.Test
```

Successful output, indicates correctly loading and calling libz3:

```console
 (define-fun x () Int
   1)
 (define-fun y () Int
   0)
```

If the above does not work, try specifying the java library path to see if that resolves the issue.

```sh
# /path/to/z3/lib/files should contain libz3 and libz3java
java -Djava.library.path=/path/to/z3/lib/files -jar /path/to/z3-plugin.jar com.github.codeql.z3.Test
# or try
cd /path/to/z3/lib/files
java -Djava.library.path=. -jar /path/to/z3-plugin.jar com.github.codeql.z3.Test
```

If `-Djava.library.path` resolves your issue, then you have the correct libraries on your system but they may be installed in the wrong place. On mac you may have SIP or rpath issues.

### Test with the CodeQL java binary

Testing with the system `java` command may be enough to resolve your issue. However, the CodeQL cli release binaries bundle a Java executable, and it's that Java executable that will ultimately run the plugin.

To test the libz3 integration with the CodeQL version of Java, locate that bundled Java executable and then perform the above steps with that executable:

```sh
# Find your codeql executable
which codeql
# Resolve symlinks:
realpath "$(which codeql)"
# Find the java executable. For example, on linux:
ls -al $(which codeql | xargs realpath | xargs dirname)/tools/linux64/java/bin/java
# test the z3 with the codeQL java executable:
$(which codeql | xargs realpath | xargs dirname)/tools/linux64/java/bin/java -Djava.library.path=/path/to/z3/lib/files -jar /path/to/z3-plugin.jar com.github.codeql.z3.Test
```

### Confirm CodeQL is loading the plugin

If the above debugging steps all succeed, you can try running a minimal example with the CodeQL plugin.

```sh
codeql query run advanced-security/z3:z3/z3test.ql --database /some/codeql/database
```

Successful output, indicates codeql plugin loads successfully, and successfully calls libz3:

```console
z3test.ql: Evaluation completed (36ms).
|                         out                         |
+-----------------------------------------------------+
| (define-fun y () Int
  0)
(define-fun x () Int
  0) |
Shutting down query evaluator.
```

## Maintainers

This project is maintained by the GitHub Advanced Security team. If you have questions or issues, please open an issue in this repository.

## Support

See [SUPPORT.md](SUPPORT.md).

## Acknowledgements

This project would not be possible without the incredible hard work of the Z3 team, the CodeQL team,
and the fantastic initial implementation of CodeQL contract validation by John Singleton ([@jsinglet](https://github.com/jsinglet)).

We would also like to extend our gratitude to [Bloomberg](https://www.techatbloomberg.com/opensource) and the fantastic folks there who helped us make this project a reality.

Software achievements are always built upon the work of others, in a large and hard working community, and we are grateful to be a part of it.
