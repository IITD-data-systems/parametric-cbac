# Memento: build the PostgreSQL extension (make) and the offline artifact builder (make builder).
PG_CONFIG ?= pg_config
FOLDERS   := $(wildcard src/*/)
PG_FLAGS  := $(shell $(PG_CONFIG) --cflags)
COMMON    := -fPIC -O3 -march=native -I$(shell $(PG_CONFIG) --includedir-server) \
             $(addprefix -I,$(FOLDERS)) -DCF_DIAGNOSTIC_COUNTERS=0
NO_LTO    := $(filter-out -flto% -ffat-lto-objects,$(PG_FLAGS)) -fno-lto
OUT       := build/clean
LIBRARY   := $(OUT)/custom_filter_new.memento.so
OBJECTS   := $(OUT)/hook.o $(OUT)/evaluator.o $(OUT)/uniform.o $(OUT)/adapter.o $(OUT)/iterator_cold.o
SOURCES   := $(wildcard src/*/*.h src/*/*.inc src/*/*.c src/*/*.cpp)

all: $(LIBRARY)

$(LIBRARY): $(OBJECTS)
	@echo "  linking $(notdir $@)"
	@$(CXX) -shared -o $@ $^

$(OUT)/hook.o: src/postgres/custom_filter_online.c $(SOURCES) | $(OUT)
	@echo "  compiling $(notdir $<)"
	@$(CC) $(PG_FLAGS) $(COMMON) -c $< -o $@
$(OUT)/evaluator.o: src/policy/policy_evaluator.cpp $(SOURCES) | $(OUT)
	@echo "  compiling $(notdir $<)"
	@$(CXX) -std=c++17 $(PG_FLAGS) $(COMMON) -c $< -o $@
$(OUT)/uniform.o: src/walk/our_pg_uniform.online.cpp $(SOURCES) | $(OUT)
	@echo "  compiling $(notdir $<)"
	@$(CXX) -std=c++17 $(PG_FLAGS) $(COMMON) -c $< -o $@
$(OUT)/adapter.o: src/postgres/our_pg_engine.adapter.cpp $(SOURCES) | $(OUT)
	@echo "  compiling $(notdir $<)"
	@$(CXX) -std=c++17 $(PG_FLAGS) $(COMMON) -c $< -o $@
# Kept out of link-time optimisation so its cold paths stay out of line.
$(OUT)/iterator_cold.o: src/walk/iterator_cold.cpp $(SOURCES) | $(OUT)
	@echo "  compiling $(notdir $<)"
	@$(CXX) -std=c++17 $(NO_LTO) $(COMMON) -c $< -o $@

$(OUT):
	@mkdir -p $@

builder:
	@$(MAKE) -C src/ranks/builder --no-print-directory

clean:
	rm -rf build src/ranks/builder/build

.PHONY: all builder clean
