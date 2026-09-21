PYTHON ?= python3
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++20 -Wall -Wextra -pthread
MASKS := 2 4 5 6 9 10 11 18 19 27 30 31 35 39

.PHONY: quick build clean replay-concise-audit replay-endpoint-local-audit replay-endpoint-zero-audit checksums

quick:
	$(PYTHON) verify_n6_orbits.py
	$(PYTHON) n6_orbit_independent_audit.py
	$(PYTHON) verify_n6_bilinear_rank17.py
	$(PYTHON) verify_n6_capacity_logs.py
	$(PYTHON) audit_n6_canonicalization.py
	$(PYTHON) gf2_canonical_key_property_test.py
	sha256sum -c SHA256SUMS

build:
	mkdir -p build
	$(CXX) $(CXXFLAGS) n6_constrained_capacity.cpp -o build/n6_constrained_capacity
	$(CXX) $(CXXFLAGS) -DLEXICOGRAPHIC_CANONICAL_AUDIT n6_constrained_capacity.cpp -o build/n6_constrained_capacity_lexaudit
	$(CXX) $(CXXFLAGS) rect56_capacity_probe.cpp -o build/rect56_capacity_probe
	$(CXX) $(CXXFLAGS) -DLOW_PIVOT_CANONICAL_AUDIT rect56_capacity_probe.cpp -o build/rect56_capacity_lowaudit
	$(CXX) $(CXXFLAGS) rect56_zero_local_blocking.cpp -o build/rect56_zero_local_blocking
	$(CXX) $(CXXFLAGS) -DLOW_PIVOT_CANONICAL_AUDIT rect56_zero_local_blocking.cpp -o build/rect56_zero_local_lowaudit

replay-concise-audit: build
	mkdir -p replay
	set -e; for mask in $(MASKS); do \
	  build/n6_constrained_capacity_lexaudit $$mask --exact \
	    > replay/n6_mask_$${mask}_lexaudit.txt; \
	done

replay-endpoint-local-audit: build
	mkdir -p replay
	build/rect56_capacity_lowaudit --exact > replay/rect56_capacity_lowaudit.txt

replay-endpoint-zero-audit: build
	mkdir -p replay
	build/rect56_zero_local_lowaudit --exhaustive > replay/rect56_zero_local_lowaudit.txt

checksums:
	sha256sum -c SHA256SUMS

clean:
	rm -rf build replay
