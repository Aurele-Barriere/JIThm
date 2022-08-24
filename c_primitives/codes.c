#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <elf.h>

#include "codes.h"
#include "prims.h"

/* Partly inspired by: https://eli.thegreenplace.net/2013/11/05/how-to-jit-an-introduction */

const size_t CODE_SIZE = 1048576; /* The size of the pages we allocate for each code snippet */

/* Type of the Jitted functions */
typedef int64_t (*JittedFunc)(); /* expects no argument, always return int64 */


/* Links the file "tmp.s" with the primitives */
/* generates file "linked.s" */
void linker() {
  char* command= (char*)malloc(300 * sizeof(char));
  sprintf (command, "sh linker.sh tmp.s %ld %ld %ld %ld %ld %ld",
	   &_PUSH, &_POP, &_SET, &_GET, &_CLOSE, &_PRINT);
  system (command);
  return;
}

/* Assembles the "linked.s" file into "linked.o" */
void assembler() {
  system("ccomp -c linked.s -o linked.o");
  return;
}


// Allocates RW memory of given size and returns a pointer to it. On failure,
// prints out the error and returns NULL. Unlike malloc, the memory is allocated
// on a page boundary so it's suitable for calling mprotect.
void* alloc_writable_memory(size_t size) {
  /* printf ("C: Allocating..."); */
  /* without MAP_ANONYMOUS, from https://stackoverflow.com/questions/34042915/what-is-the-purpose-of-map-anonymous-flag-in-mmap-system-call */
  int fd = open("/dev/zero", O_RDWR); 
  void* ptr = mmap(0, size,
                   PROT_READ | PROT_WRITE,
                   MAP_PRIVATE , fd, 0);
  /* printf ("Done at %ld\n", ptr); */
  if (ptr == (void*)-1) {
    perror("mmap");
    return NULL;
  }
  return ptr;
}

// Sets a RX permission on the given memory, which must be page-aligned.
// Returns 0 on success. On failure, prints out the error and returns -1.
int make_memory_executable(void* m, size_t size) {
  if (mprotect(m, size, PROT_READ | PROT_EXEC) == -1) {
    perror("mprotect");
    return -1;
  }
  return 0;
}

/* Reads from file "linked.o" the .text section */
/* Installs the corresponding machine bytes at m */
void emit_code_into_memory(unsigned char* m) {
  FILE* ElfFile = NULL;
  char* SectNames = NULL;
  Elf64_Ehdr elfHdr;
  Elf64_Shdr sectHdr;
  uint32_t idx;
  if((ElfFile = fopen("linked.o", "r")) == NULL) { /* reading the object file */
    perror("Install: Error opening file:");
    exit(1);
  }
  // read ELF header, first thing in the file
  fread(&elfHdr, 1, sizeof(Elf64_Ehdr), ElfFile);
  // read Section header
  fseek(ElfFile, elfHdr.e_shoff + elfHdr.e_shstrndx * sizeof(sectHdr), SEEK_SET);
  fread(&sectHdr, 1, sizeof(sectHdr), ElfFile);
  // next, read the section, string data
  SectNames = malloc(sectHdr.sh_size);
  fseek(ElfFile, sectHdr.sh_offset, SEEK_SET);
  fread(SectNames, 1, sectHdr.sh_size, ElfFile);
  char text[] = ".text";	/* the section we want to find */
  // read all section headers
  for (idx = 0; idx < elfHdr.e_shnum; idx++) {
    const char* name = "";
    fseek(ElfFile, elfHdr.e_shoff + idx * sizeof(sectHdr), SEEK_SET);
    fread(&sectHdr, 1, sizeof(sectHdr), ElfFile);
    /* if (sectHdr.sh_name); */
    name = SectNames + sectHdr.sh_name; /* section name */
    if (strcmp(text,name)==0) {		/* found the .text section */
      fseek(ElfFile, sectHdr.sh_offset, SEEK_SET);
      fread(m, 1, sectHdr.sh_size, ElfFile); /* writing the bytes of .text section */
      return;
    }
  }
  perror("Couldn't find a .text section");
  exit(1);
}

// Allocates RW memory, emits the code into it and sets it to RX
// Returns the address of the Jitted func
JittedFunc emit_to_rw_and_rx() {
  void* m = alloc_writable_memory(CODE_SIZE);
  emit_code_into_memory(m);	/* reading from linked.o */
  make_memory_executable(m, CODE_SIZE);
  JittedFunc func = m;
  return func;
}

/* Links the file at "tmp.s" into "linked.s"
   Assembles it into "linked.o"
   Installs it into memory & make executable
   Returns the corresponding function pointer */
JittedFunc link_assemble_and_install() {
  linker();
  assembler();
  JittedFunc func = emit_to_rw_and_rx();
  return func;
}

/* Runs the code installed at address func */
int64_t run_code (JittedFunc func) {
  int64_t result = func();
  return result;
}
