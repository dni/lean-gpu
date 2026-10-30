# make        CPU reference build (runs anywhere)
# make cuda   GPU build (needs nvcc)
BUILD := build
CFLAGS := -O2 -Wall -Wextra

$(BUILD)/farkas: main.c solve_cpu.c exact.c farkas.h exact.h | $(BUILD)
	$(CC) $(CFLAGS) -o $@ main.c solve_cpu.c exact.c -lm -lgmp

cuda: main.c solve_cpu.c exact.c solve.cu farkas.h exact.h | $(BUILD)
	nvcc -O2 -DUSE_CUDA -o $(BUILD)/farkas main.c solve_cpu.c exact.c solve.cu -lm -lgmp

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)

.PHONY: cuda clean
