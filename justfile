all: build doc

# build the library
build:
    cargo build

# run tests
test:
    cargo test
    cargo test --example simple

# generate all documentation
doc: doc-api doc-book

# generate API documentation
doc-api: 
    cargo doc

# generate the guide book
doc-book:
    mdbook build book

# clean all generated files
clean:
    cargo clean
    mdbook clean book
