#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <sys/mman.h>
#include <unistd.h>
#include <sys/types.h>
#include <stdint.h>
#include <string.h>



/* ------------ Block Cache ------------ */

#define MAX_BLOCKS 1000

struct blockref_t
{
    /* Where the referenced block starts in the source code, for jitting the block */
    int start_index;

    /* Where the referenced block ends in the source code, for jitting the block */
    int end_index;

    /* Whether this blockref is optimised - for debugging only */
    bool optimised;

    /* Address to call from the translation, accessed by the indirect call instruction */
    void *call_addr;

    /* Address immediately after the call in the translation,
       used to match with return address so the slow path knows
       this is the relevant blockref */
    void *ret_addr;
};

struct block_t
{
    /* Where this block starts in the source code, for finding the block */
    int index;

    /* Start index of parent block, for unlinking parent's reference when deleting this block */
    int parent_index;

    /* Area of associated memory, for freeing the block's resources */
    void *mem;

    /* Pointer into code in 'mem' area, for executing and finding the block by code address */
    void *code;

    /* Pointer after end of code, for finding the block by code address */
    void *code_end;

    /* Number of inner block refs */
    int blockref_count;

    /* Pointer to start of block ref list stored in 'mem' area */
    struct blockref_t *blockrefs;
};


/* Block cache: */
static struct block_t blocks[MAX_BLOCKS];
static int next_block_ptr = 0;

/* Pointer into block-resolving code */
void xlate_call_slow();

/* Initialize all blocks to invalid */
static void block_init()
{
    for(int i = 0; i < MAX_BLOCKS; i++)
    {
        /* Make this block invalid */
        blocks[i].index = -1;
    }
}

/* Given an index, find a block or NULL if translation is not present */
static struct block_t *block_lookup(int idx)
{
    for(int i = 0; i < MAX_BLOCKS; i++)
    {
        if(blocks[i].index != -1 && blocks[i].index == idx)
        {
            return &blocks[i];
        }
    }

    return NULL;
}

/* Find a block by an address in its translation */
static struct block_t *block_lookup_by_code_address(void *address)
{

    for(int i = 0; i < MAX_BLOCKS; i++)
    {
        if(address >= blocks[i].code && address < blocks[i].code_end)
        {
            return &blocks[i];
        }
    }

    return NULL;
}

/* Unlink a blockref, downgrading the call to a slow path call */
static void block_unlink(struct blockref_t *to_unlink)
{
    to_unlink->optimised = false;
    to_unlink->call_addr = xlate_call_slow;
}

/* Delete a block */
static void block_remove(struct block_t *to_remove)
{
    /* Unlink parent from it if the parent still exists */
    struct block_t *parent = block_lookup(to_remove->parent_index);
    if(parent)
    {
        for(int i = 0; i < parent->blockref_count; i++)
        {
            if(parent->blockrefs[i].start_index == to_remove->index)
            {
                block_unlink(&parent->blockrefs[i]);
            }
        }
    }

    /* Make it invalid */
    to_remove->index = -1;

    /* Free associated memory */
    free(to_remove->mem);

    /* Put NULLs in to avoid confusing things */
    to_remove->blockrefs = NULL;
    to_remove->code = NULL;
    to_remove->code_end = NULL;
}

/* Allocate a new block - 'mem' must contain code and blockrefs list.
 * Set parent_index to -1 if this is the top level block */
static struct block_t *block_new(int idx, void *mem, struct blockref_t *blockrefs, int blockref_count, void *code, void *code_end, int parent_index)
{

    struct block_t *b = &blocks[next_block_ptr];
    next_block_ptr = (next_block_ptr + 1) % MAX_BLOCKS;
    if(b->index != -1)
    {
        block_remove(b);
    }

    b->index = idx;
    b->blockref_count = blockref_count;
    b->mem = mem;
    b->blockrefs = blockrefs;
    b->code = code;
    b->code_end = code_end;
    b->parent_index = parent_index;
    return b;
}

/* ------------ End of Block Cache ------------ */


/* ------------ Translation ------------ */


/* Maximum number of bytes that a translation can produce */
#define XLATE_MAX 64

/* Location to spill RAX to when entering C code */
uint64_t xlate_rax_spill;

/* , and . operations, respectively */
void xlate_input_char();
void xlate_output_char();

/* Translate a BF operation to machine code,
 * returning number of machine code bytes generated */
static int xlate_operation(char op, char *output)
{

    char *output_start = output;
    uint32_t *offset;

    switch(op)
    {
    case '+':
        // inc (%rax)
        *output++ = 0x48;
        *output++ = 0xff;
        *output++ = 0x00;
        break;
    case '-':
        // dec (%rax)
        *output++ = 0x48;
        *output++ = 0xff;
        *output++ = 0x08;
        break;
    case '>':
        // inc %rax
        *output++ = 0x48;
        *output++ = 0xff;
        *output++ = 0xc0;
        break;
    case '<':
        // dec %rax
        *output++ = 0x48;
        *output++ = 0xff;
        *output++ = 0xc8;
        break;
    case '.':
        // mov %rax,xlate_rax_spill(%rip)
        *output++ = 0x48;
        *output++ = 0x89;
        *output++ = 0x05;
        offset = (uint32_t*)output;
        output += 4;
        *offset = ((uint64_t)(void*)&xlate_rax_spill)-((uint64_t)(void*)output);

        // callq xlate_output_char
        *output++ = 0xe8;
        offset = (uint32_t*)output;
        output += 4;
        *offset = ((uint64_t)(void*)&xlate_output_char)-((uint64_t)(void*)output);

        // mov xlate_rax_spill(%rip),%rax
        *output++ = 0x48;
        *output++ = 0x8b;
        *output++ = 0x05;
        offset = (uint32_t*)output;
        output += 4;
        *offset = ((uint64_t)(void*)&xlate_rax_spill)-((uint64_t)(void*)output);
        break;
    case ',':
        // mov %rax,xlate_rax_spill(%rip)
        *output++ = 0x48;
        *output++ = 0x89;
        *output++ = 0x05;
        offset = (uint32_t*)output;
        output += 4;
        *offset = ((uint64_t)(void*)&xlate_rax_spill)-((uint64_t)(void*)output);

        // callq xlate_input_char
        *output++ = 0xe8;
        offset = (uint32_t*)output;
        output += 4;
        *offset = ((uint64_t)(void*)&xlate_input_char)-((uint64_t)(void*)output);

        // mov xlate_rax_spill(%rip),%rax
        *output++ = 0x48;
        *output++ = 0x8b;
        *output++ = 0x05;
        offset = (uint32_t*)output;
        output += 4;
        *offset = ((uint64_t)(void*)&xlate_rax_spill)-((uint64_t)(void*)output);
        break;
    }

    return output - output_start;
}

/* Translate a block call, providing the address of the address to call */
static int xlate_block_call(char *output, void **call_addr, void **ret_addr)
{
    char *output_start = output;

    // jump_start:

    // callq *call_addr(%rip)
    *output++ = 0xff;
    *output++ = 0x15;
    uint32_t *offset = (uint32_t*)output;
    output += 4;
    *offset = ((uint64_t)(void*)call_addr)-((uint64_t)(void*)output);

    /* We need this to find the blockref */
    *ret_addr = output;

    // mov (%rax), %rbx
    *output++ = 0x48;
    *output++ = 0x8b;
    *output++ = 0x18;

    // test %rbx,%rbx
    *output++ = 0x48;
    *output++ = 0x85;
    *output++ = 0xdb;

    // jne jump_start
    *output++ = 0x75;
    *output++ = 0xf2;

    return output - output_start;
}

/* Update a block ref such that it calls a given target address */
static void xlate_patch_block_ref(struct blockref_t *blockref, char *target_address, bool is_optimised)
{
    /* Patch in absolute address */
    blockref->call_addr = (void*)target_address;
    blockref->optimised = is_optimised;
}

static char xlate_dummy_buffer[XLATE_MAX];

/* Do a dummy translation to collect code size and number of blockrefs for a new block */
static size_t xlate_measure_block(char *text, int start_idx, int end_idx, int *blockrefs)
{
    int depth = 0;
    size_t size = 0;

    for(int idx = start_idx; idx < end_idx; idx++)
    {
        if(text[idx] == '[')
        {
            depth++;
            if(depth == 1)
            {
                /* Just went to depth 1 - we need a new block ref */
                (*blockrefs)++;
                size += xlate_block_call(xlate_dummy_buffer, (void*)xlate_dummy_buffer, (void*)xlate_dummy_buffer);
            }
        }
        else if(text[idx] == ']')
        {
            depth--;
        }
        else if(depth == 0)
        {
            size += xlate_operation(text[idx], xlate_dummy_buffer);
        }
    }

    // retq
    size += 1;

    return size;
}

/* Actually translate a new block, filling in the blockref structures and emitting code to output. */
static void xlate_write_block(char *text, int start_idx, int end_idx, char *output, struct blockref_t *blockrefs)
{
    int depth = 0;
    char *ptr = output;
    int blockref_count = 0;

    struct blockref_t *current_blockref;

    for(int idx = start_idx; idx < end_idx; idx++)
    {
        if(text[idx] == '[')
        {
            depth++;
            if(depth == 1)
            {
                /* Write the call, passing in the address of the call address and also reading the ret address, immediately after the call instruction */
                current_blockref = &blockrefs[blockref_count++];
                ptr += xlate_block_call(ptr, &current_blockref->call_addr, &current_blockref->ret_addr);
                current_blockref->call_addr = xlate_call_slow;
                current_blockref->start_index = idx + 1;
                current_blockref->optimised = false;
            }
        }
        else if(text[idx] == ']')
        {
            depth--;
            if(depth == 0)
            {
                current_blockref->end_index = idx;
            }
        }
        else if(depth == 0)
        {
            ptr += xlate_operation(text[idx], ptr);
        }
    }

    // retq
    *ptr++ = 0xc3;
}

/* Given a start and end index, acquire a block by either returning an existing one, or generating a new one */
static struct block_t *xlate_get_or_make_block(char *text, int start_idx, int end_idx, int parent_index)
{
    struct block_t *b = block_lookup(start_idx);
    if(!b)
    {
        /* Need to translate a new block */

        /* Measure code size and block refs */
        int blockref_count = 0;
        size_t code_size = xlate_measure_block(text, start_idx, end_idx, &blockref_count);

        /* Allocate memory for blockrefs and code using malloc */
        size_t blockrefs_size = blockref_count * sizeof(struct blockref_t);
        void *mem = malloc( blockrefs_size + code_size);
        struct blockref_t *blockrefs = (struct blockref_t *)mem;
        char *code = (char*)mem + blockrefs_size;

        /* Make the memory executable */
        mprotect(code, code_size, PROT_READ | PROT_WRITE | PROT_EXEC);

        /* Generate the actual translation for this block */
        xlate_write_block(text, start_idx, end_idx, code, blockrefs);

        /* Add it to the block cache */
        b = block_new(start_idx, mem, blockrefs, blockref_count, code, code + code_size, parent_index);
    }

    return b;
}


/* Given a return address within a translation, find the corresponding caller blockref.
 * Also get the caller block and blockref number, for convenience. */
static struct blockref_t *xlate_find_caller_blockref_by_return_address(void *return_address, struct block_t **caller, int *blockref_num)
{
    *caller = block_lookup_by_code_address(return_address);

    if(!(*caller))
    {
        return NULL;
    }

    for(int i = 0; i < (*caller)->blockref_count; i++)
    {
        if((*caller)->blockrefs[i].ret_addr == return_address)
        {
            *blockref_num = i;
            return &((*caller)->blockrefs[i]);
        }
    }
    return NULL;
}


/* ------------ End of Translation ------------ */



/* ------------ Runtime ------------ */

static char *runtime_program_text;

/* I/O implementations */
void xlate_input_char()
{
    char *dest = (char*)(void*)xlate_rax_spill;
    *dest = getchar();
}

void xlate_output_char()
{
    putchar(*(char*)(void*)xlate_rax_spill);
}


/* Called from C, jumps to a pc with a given stack pointer */
void runtime_enter(void *pc, void **stack_pointer);

/* Called from ASM,
 * %rdi has a pointer to top of stack */
void runtime_call_slow(void **stack_pointer)
{
    /* Search for the block that called us */
    void *return_address = *stack_pointer;

    struct block_t *caller = NULL;
    int caller_blockref_num = -1;
    struct blockref_t *caller_blockref = xlate_find_caller_blockref_by_return_address(return_address, &caller, &caller_blockref_num);
    if(!caller_blockref)
    {
        printf("Unable to find caller blockref. How did we get here?");
        exit(1);
    }
    int caller_index = caller->index;


    /* Generate the target block, potentially destroying the caller.
     * Note that so long as the source code doesn't change, caller_blockref_num will still be meaningful
     * even if the pointers aren't */
    struct block_t *target = xlate_get_or_make_block(runtime_program_text, caller_blockref->start_index, caller_blockref->end_index, caller_index);

    /* Ensure that caller still has a translation */
    caller = block_lookup(caller_index);
    if(caller)
    {
        /* Patch the caller's jumpsite so it's optimised next time */
        xlate_patch_block_ref(&caller->blockrefs[caller_blockref_num], target->code, true);
    }

    /* Go and execute our new block */
    runtime_enter(target->code, stack_pointer);

}

/* ------------ End of Runtime ------------ */


#define STACK_SIZE 16384
#define MEM_SIZE 16384


void *my_stack[STACK_SIZE];

char *my_mem[MEM_SIZE];


int main(int argc, char **argv)
{
    (void)argc;
    (void)argv;

    block_init();

    /* Source code */
    runtime_program_text = "++++++++++++++++++++++++++++[.-]++++++++++++++++++++++++++++[.-]+++++++++++++[.-]++.++.++.[.,]";

    /* JIT the source code as a single block */
    struct block_t *main_block = xlate_get_or_make_block(runtime_program_text, 0, strlen(runtime_program_text), -1);

    /* Set up RAX to point into memory */
    xlate_rax_spill = (uint64_t)(void*)my_mem;

    /* Jump to the jitted code */
    runtime_enter(main_block->code, my_stack + STACK_SIZE - 2);

    /* Never reach here */
    return 1;
}
