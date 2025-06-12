# Contributing

Hi there! We're thrilled that you'd like to contribute to this project. Your help is essential for keeping it great.

Contributions to this project are [released](https://help.github.com/articles/github-terms-of-service/#6-contributions-under-repository-license) to the public under the [project's open source license](LICENSE.md).

Please note that this project is released with a [Contributor Code of Conduct][code-of-conduct]. By participating in this project you agree to abide by its terms.

## Scope

This project considers the following contributions:

1. **Documentation improvements** including **installation instructions** and **troubleshooting tips**.
1. **Bug fixes**: For instance, fixing bugs related to generating incorrect z3 code.
1. **Additional library support**: typically, modeling assertions in new libraries.
1. **Additional expression support**: modeling new kinds of expressions as z3 contracts.
1. **Additional language support**: This project currently only support C++, but we would welcome
    any contributions that expand our support to other languages.
1. **Improved value modeling**: Cases where the constraints given to z3 are imprecise and can be
    improved to make constraint violation more precise.
1. **Other interesting usages of z3**: If you have an interesting use case for z3 that is not
    covered by the above, please feel free to open an issue to discuss it!

## Submitting a pull request

The next step, after registering and discussing your improvement, is proposing the improvement in a pull request.

1. [Fork][fork] and clone the repository
1. Configure and install the [CodeQL CLI](https://github.com/github/codeql-cli-binaries/releases).
1. Create a new branch: `git checkout -b my-branch-name`
1. Make your changes and commit them: `git commit -m 'Add some feature'`
1. Ensure the files are appropriately formatted: QL files should be formatted with `codeql query format`.
1. Create new tests for any new features or changes to existing features. Ensure all existing tests pass. Tests can be run with `codeql test run $DIR`, where `$DIR` is either `/common/test` or `cpp/test`. Currently there are no tests for the z3 java plugin itself, but if complex logic is added there it then java tests should be added in `plugin/src/test` as well.
1. Push to your fork and [submit a draft pull request](https://github.com/advanced-security/codeql-contracts-z3/compare). Make sure to select **Create Draft Pull Request**.
1. Address failed checks, if any.
1. Mark the [pull request ready for review](https://docs.github.com/en/pull-requests/collaborating-with-pull-requests/proposing-changes-to-your-work-with-pull-requests/changing-the-stage-of-a-pull-request#marking-a-pull-request-as-ready-for-review).
1. Pat your self on the back and wait for your pull request to be reviewed and merged.

Here are a few things you can do that will increase the likelihood of your pull request being accepted:

- Ensure all PR checks succeed.
- Keep your change as focused as possible. If there are multiple changes you would like to make that are not dependent upon each other, consider submitting them as separate pull requests.
- Write a [good commit message](http://tbaggery.com/2008/04/19/a-note-about-git-commit-messages.html).

## Building the plugin

This is only necessary if you are altering the z3 plugin itself -- for instance, updating z3 or adding a new plugin API method.

The plugin API is not public. However, it is described briefly here for those who have access: https://github.com/github/semmle-code/pull/46712/files

### Requirements

Building the plugin requires that you have Java + Maven installed.

### Building z3 java bindings

Your package manager may ship the java bindings (in the form of a `.jar` file) when you install z3. However, homebrew does not. Therefore, these instructions will detail building z3 from source with java bindings.

These build instructions are also detailed on the z3 project page (https://github.com/Z3Prover/z3).

Either git clone z3 into a directory, or download and extract the source tar.gz for an appropriate version of z3. After we have the sources, we build it from source including a flag to build the java bindings.

Assuming a tarball named `z3-source` in your `Downloads` directory:

```sh
tar -xzf ~/Downloads/z3-source.tar
cd z3-source
python mk_make.py --java
cd build
make com.microsoft.z3.jar -j 16
```

This jar can then be installed into the local maven repository:

```sh
mvn install:install-file \
  -Dfile=com.microsoft.z3.jar \
  -DgroupId=com.microsoft \
  -DartifactId=z3 \
  -Dversion=4.14.1 \
  -Dpackaging=jar
```

And now, from the `plugin` directory in the project root, you should be ready to build the codeql plugin itself:

```sh
cd $PROJECT_ROOT/plugin
mvn package
```

The resulting artifact (the plugin jar file) will be built and located in `/plugin/target/z3-plugin-${VERSION}-SNAPSHOT.jar`. This can be installed into `$CODEQL_HOME/tools` as per default instructions in [README.md](README.md).

## Test your local install

```sh
codeql query run common/src/z3/z3test.ql --database /path/to/some/database
```

Success:

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

## Resources

- [How to Contribute to Open Source](https://opensource.guide/how-to-contribute/)
- [Using Pull Requests](https://help.github.com/articles/about-pull-requests/)
- [GitHub Help](https://help.github.com)

[fork]: https://github.com/advanced-security/codeql-contracts-z3/fork
[code-of-conduct]: CODE_OF_CONDUCT.md
