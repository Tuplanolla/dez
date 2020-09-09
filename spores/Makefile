HIDE:=$(if $(VERBOSE),,@)
SHOW:=$(if $(VERBOSE),@ true||,@)

all :: main
	$(SHOW) echo STAT $^
.PHONY: all

clean ::
	$(SHOW) echo CLEAN CXX
	$(HIDE) find . -maxdepth 1 -type f '(' \
	-name '*.o' \
	')' -exec $(RM) '{}' '+'
	$(SHOW) echo CLEAN main
	$(HIDE) $(RM) main
.PHONY: clean

run ::
	$(SHOW) echo RUN main
	$(HIDE) ./main
.PHONY: run

main :: main.o
	$(CXX) $(CXXFLAGS) -o $@ $<

main.o :: main.cxx
	$(CXX) $(CXXFLAGS) -c -o $@ $<
