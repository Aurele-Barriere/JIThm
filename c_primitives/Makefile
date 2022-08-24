CC= ccomp
CFILES= stack.c heap.c prims.c codes.c c_lib.c
HEADERS= stack.h heap.h prims.h codes.h

all: c_lib.o

c_lib.o: $(CFILES) $(HEADERS)
	$(CC) -c -I/usr/local/lib/ocaml $(CFILES)

clean:
	-@rm *.o

