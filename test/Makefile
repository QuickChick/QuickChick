TESTS=mutation.test plugin.test

.PHONY: test $(TESTS)

test: $(TESTS)

MUTATION=mutation

mutation.test:
	cd $(MUTATION)/; sh $(MUTATION).sh

plugin.test:
	cd plugin/; sh plugin.sh

rand.test:
	cd rand/; sh rand.sh
	@echo "NOW RUN THIS: ./test/rand/randexe|dieharder -a -g 200|tee dhreport.txt"
