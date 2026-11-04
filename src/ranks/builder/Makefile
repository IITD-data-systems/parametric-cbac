# Offline builder: a PostgreSQL extension that extracts per-column ranks, and
# emit_universe, which merges compared columns into one rank universe.
PG_CONFIG ?= pg_config
INCLUDES  := -I$(shell $(PG_CONFIG) --includedir-server) -I../
CFLAGS    := -fPIC -O2 $(shell $(PG_CONFIG) --cflags) -Wno-declaration-after-statement
CXXFLAGS  := -fPIC -O2 $(shell $(PG_CONFIG) --cflags)
OBJECTS   := build/artifact_builder.o build/artifact_builder_helper.o build/policy_spec.o build/emit_invidx_pg.o

all: build/artifact_builder.so build/emit_universe

build/artifact_builder.so: $(OBJECTS)
	@echo "  linking $(notdir $@)"
	@$(CXX) -shared -o $@ $^

build/%.o: %.c | build
	@echo "  compiling $(notdir $<)"
	@$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

build/artifact_builder_helper.o: artifact_builder_helper.cpp | build
	@echo "  compiling $(notdir $<)"
	@$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

build/emit_invidx_pg.o: emit_invidx_pg.cpp | build
	@echo "  compiling $(notdir $<)"
	@$(CXX) $(CXXFLAGS) $(INCLUDES) -std=c++17 -c $< -o $@

build/emit_universe: emit_universe.cpp | build
	@echo "  compiling $(notdir $<)"
	@$(CXX) -std=c++17 -O3 -march=native -I../ $< -o $@

build:
	@mkdir -p build

clean:
	rm -rf build
