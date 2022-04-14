TESTS=mutation.test plugin.test internal.test

.PHONY: test $(TESTS)

test: $(TESTS)

MUTATION=mutation

mutation.test:
	cd mutation; sh run.sh

plugin.test:
	cd plugin; sh run.sh

internal.test:
	cd internal; sh run.sh
