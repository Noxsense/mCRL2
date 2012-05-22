/*{{{  includes */

#include <cstdio>
#include <stdlib.h>
#include <assert.h>
#include <stdexcept>

#ifdef WIN32
#include <fcntl.h>
#include <io.h>
#endif

#include "mcrl2/utilities/logger.h"
#include "mcrl2/atermpp/detail/bafio.h"
#include "mcrl2/atermpp/detail/memory.h"
#include "mcrl2/atermpp/detail/util.h"
#include "mcrl2/atermpp/detail/byteio.h"
#include "mcrl2/atermpp/aterm_int.h"

/*}}}  */

namespace atermpp
{


/**
 * Calculate the number of unique symbols.
 */

/*{{{  static size_t calcUniqueAFuns(aterm t) */

static size_t calcUniqueAFuns(const aterm &t, std::set<aterm> &visited)
{
  size_t nr_unique = 0;
  size_t  i, arity;
  function_symbol sym;
  aterm_list list;

  // if (IS_MARKED(t->header))
  if (visited.count(t)>0)
  {
    return 0;
  }

  switch (t.type())
  {
    case AT_INT:
      if (!function_symbol::at_lookup_table[AS_INT.number()]->count++)
      {
        nr_unique = 1;
      }
      break;

    case AT_APPL:
      sym = t.function(); 
      assert(function_symbol::at_lookup_table.size()>sym.number());
      nr_unique = function_symbol::at_lookup_table[sym.number()]->count>0 ? 0 : 1;
      function_symbol::at_lookup_table[sym.number()]->count++;
      // AT_markAFun(sym);
      arity = sym.arity();
      for (i = 0; i < arity; i++)
      {
        nr_unique += calcUniqueAFuns(static_cast<aterm_appl>(t)(i),visited);
      }
      break;

    case AT_LIST:
      list = static_cast<aterm_list>(t);
      while (list!=aterm_list() && visited.count(list)==0 /* !IS_MARKED(list->header)*/ )
      {
        // SET_MARK(list->header);
        visited.insert(list);
        if (!function_symbol::at_lookup_table[AS_LIST.number()]->count++)
        {
          nr_unique++;
        }
        nr_unique += calcUniqueAFuns(list.head(),visited);
        list = list.tail();
      }
      if (list==aterm_list() && visited.count(list)==0 /* !IS_MARKED(list->header)*/ )
      {
        // SET_MARK(list->header);
        visited.insert(list);
        if (!function_symbol::at_lookup_table[AS_EMPTY_LIST.number()]->count++)
        {
          nr_unique++;
        }
      }
      break;
  }

  visited.insert(t);
  // SET_MARK(t->header);

  return nr_unique;
}

static size_t AT_calcUniqueAFuns(const aterm &t)
{
  std::set<aterm> visited;
  size_t result = calcUniqueAFuns(t,visited);
  // AT_unmarkIfAllMarked(t);

  return result;
}

/*{{{  defines */

static const size_t BAF_MAGIC = 0xbaf;
static const size_t BAF_VERSION = 0x0300;      /* version 3.0 */
//#define BAF_MAGIC 0xbaf
//#define BAF_VERSION 0x0300      /* version 3.0 */

static const size_t BAF_DEFAULT_TABLE_SIZE = 1024;

static const size_t BAF_LIST_BATCH_SIZE = 64;

static const size_t SYMBOL_OFFSET = 10;

//#define SYM_INDEX(n)      (((n)-SYMBOL_OFFSET)/2)
//#define SYM_COMMAND(n)    ((n)*2 + SYMBOL_OFFSET)

/* Maximum # of arguments to reserve space for on the stack in read_term */
static const size_t MAX_STACK_ARGS = 4;

/*}}}  */
/*{{{  types */

typedef struct _trm_bucket
{
  struct _trm_bucket* next;
  aterm t;
} trm_bucket;

typedef struct _top_symbol
{
  struct _top_symbol* next;
  function_symbol s;

  size_t index;
  size_t count;

  size_t code_width;
  size_t code;
} top_symbol;

class top_symbols_t
{
  public:
    size_t      nr_symbols;
    std::vector<top_symbol> symbols;

    size_t toptable_size;
    top_symbol** toptable;

    top_symbols_t():
      nr_symbols(0),
      toptable_size(0),
      toptable(NULL)
    {}

};

class sym_entry
{
  public:
    function_symbol id;
    size_t arity;

    size_t nr_terms;
    trm_bucket* terms;

    std::vector<top_symbols_t> top_symbols; /* top symbols occuring in this symbol */

    size_t termtable_size;
    trm_bucket** termtable;

    size_t term_width;

    size_t cur_index;
    size_t nr_times_top; /* # occurences of this symbol as topsymbol */

    sym_entry* next_topsym;

    sym_entry():
      arity(0),
      nr_terms(0),
      terms(NULL),
      top_symbols(0),
      termtable_size(0),
      termtable(NULL),
      term_width(0),
      cur_index(0),
      nr_times_top(0)
    {}
};

class sym_read_entry
{
  public:
    function_symbol   sym;
    size_t arity;
    size_t nr_terms;
    size_t    term_width;
    std::vector<aterm> terms;
    size_t*   nr_topsyms;
    size_t*   sym_width;
    size_t**  topsyms;

    sym_read_entry():
       arity(0),
       nr_terms(0),
       term_width(0),
       nr_topsyms(NULL),
       sym_width(NULL),
       topsyms(NULL)
    {
    }

};

/*}}}  */
/*{{{  variables */

char bafio_id[] = "$Id$";

static size_t nr_unique_symbols = 0;
static std::vector<sym_read_entry> read_symbols;
static std::vector<sym_entry> sym_entries;
static sym_entry* first_topsym = NULL;

static char* text_buffer = NULL;
static size_t text_buffer_size = 0;

static unsigned char bit_buffer = '\0';
static size_t  bits_in_buffer = 0; /* how many bits in bit_buffer are used */

/*}}}  */

/*{{{  void AT_getBafVersion(int *major, int *minor) */

void
AT_getBafVersion(int* major, int* minor)
{
  *major = BAF_VERSION >> 8;
  *minor = BAF_VERSION & 0xff;
}

/*}}}  */

/*{{{  static int writeIntToBuf(unsigned int val, unsigned char *buf) */

static
size_t
writeIntToBuf(const size_t val, unsigned char* buf)
{
  if (val < (1 << 7))
  {
    buf[0] = (unsigned char) val;
    return 1;
  }

  if (val < (1 << 14))
  {
    buf[0] = (unsigned char)((val >>  8) | 0x80);
    buf[1] = (unsigned char)((val >>  0) & 0xff);
    return 2;
  }

  if (val < (1 << 21))
  {
    buf[0] = (unsigned char)((val >> 16) | 0xc0);
    buf[1] = (unsigned char)((val >>  8) & 0xff);
    buf[2] = (unsigned char)((val >>  0) & 0xff);
    return 3;
  }

  if (val < (1 << 28))
  {
    buf[0] = (unsigned char)((val >> 24) | 0xe0);
    buf[1] = (unsigned char)((val >> 16) & 0xff);
    buf[2] = (unsigned char)((val >>  8) & 0xff);
    buf[3] = (unsigned char)((val >>  0) & 0xff);
    return 4;
  }

  if (sizeof(size_t)>4 && val>((size_t)1<<4*sizeof(size_t)))
  {
    mCRL2log(mcrl2::log::warning) << "losing precision of integers when writing to .baf file" << std::endl;
  }

  buf[0] = 0xf0;
  buf[1] = (unsigned char)((val >> 24) & 0xff);
  buf[2] = (unsigned char)((val >> 16) & 0xff);
  buf[3] = (unsigned char)((val >>  8) & 0xff);
  buf[4] = (unsigned char)((val >>  0) & 0xff);
  return 5;
}

/*}}}  */

/*{{{  static int writeBits(size_t val, int nr_bits, byte_writer *writer) */

static int writeBits(size_t val, const size_t nr_bits, byte_writer* writer)
{
  size_t cur_bit;

  for (cur_bit=0; cur_bit<nr_bits; cur_bit++)
  {
    bit_buffer <<= 1;
    bit_buffer |= (val & 0x01);
    val >>= 1;
    if (++bits_in_buffer == 8)
    {
      if (write_byte((int)bit_buffer, writer) == -1)
      {
        return -1;
      }
      bits_in_buffer = 0;
      bit_buffer = '\0';
    }
  }

  if (val)
  {
    return -1;
  }

  /* Ok */
  return 0;
}

/*}}}  */
/*{{{  static int flushBitsToWriter(byte_writer *writer) */

static
int
flushBitsToWriter(byte_writer* writer)
{
  int result = 0;
  if (bits_in_buffer > 0)
  {
    size_t left = 8-bits_in_buffer;
    bit_buffer <<= left;
    result = (write_byte((int)bit_buffer, writer) == EOF) ? -1 : 0;
    bits_in_buffer = 0;
    bit_buffer = '\0';
  }

  return result;
}

/*}}}  */
/*{{{  static int readBits(size_t *val, int nr_bits, byte_reader *reader) */

static
int
readBits(size_t* val, const size_t nr_bits, byte_reader* reader)
{
  size_t cur_bit, mask = 1;

  *val = 0;
  for (cur_bit=0; cur_bit<nr_bits; cur_bit++)
  {
    if (bits_in_buffer == 0)
    {
      int val = read_byte(reader);
      if (val == EOF)
      {
        return -1;
      }
      bit_buffer = (char) val;
      bits_in_buffer = 8;
    }
    *val |= (bit_buffer & 0x80 ? mask : 0);
    mask <<= 1;
    bit_buffer <<= 1;
    bits_in_buffer--;
  }

  /* Ok */
  return 0;
}

/*}}}  */
/*{{{  static int writeInt(size_t val, byte_writer *writer) */

static bool writeInt(const size_t val, byte_writer* writer)
{
  size_t nr_items;
  unsigned char buf[8];

  nr_items = writeIntToBuf(val, buf);
  if (write_bytes((char*)buf, nr_items, writer) != nr_items)
  {
    return false;
  }

  /* Ok */
  return true;
}

/*}}}  */
/*{{{  static int readInt(size_t *val, byte_reader *reader) */

static int readInt(size_t* val, byte_reader* reader)
{
  int buf[8];

  /* Try to read 1st character */
  if ((buf[0] = read_byte(reader)) == EOF)
  {
    return EOF;
  }

  /* Check if 1st character is enough */
  if ((buf[0] & 0x80) == 0)
  {
    *val = buf[0];
    return 1;
  }

  /* Try to read 2nd character */
  if ((buf[1] = read_byte(reader)) == EOF)
  {
    return EOF;
  }

  /* Check if 2nd character is enough */
  if ((buf[0] & 0x40) == 0)
  {
    *val = buf[1] + ((buf[0] & ~0xc0) << 8);
    return 2;
  }

  /* Try to read 3rd character */
  if ((buf[2] = read_byte(reader)) == EOF)
  {
    return EOF;
  }

  /* Check if 3rd character is enough */
  if ((buf[0] & 0x20) == 0)
  {
    *val = buf[2] + (buf[1] << 8) + ((buf[0] & ~0xe0) << 16);
    return 3;
  }

  /* Try to read 4th character */
  if ((buf[3] = read_byte(reader)) == EOF)
  {
    return EOF;
  }

  /* Check if 4th character is enough */
  if ((buf[0] & 0x10) == 0)
  {
    *val = buf[3] + (buf[2] << 8) + (buf[1] << 16) +
           ((buf[0] & ~0xf0) << 24);
    return 4;
  }

  /* Try to read 5th character */
  if ((buf[4] = read_byte(reader)) == EOF)
  {
    return EOF;
  }

  /* Now 5th character should be enough */
  *val = buf[4] + (buf[3] << 8) + (buf[2] << 16) + (buf[1] << 24);
  return 5;
}

/*}}}  */
/*{{{  static int writeString(const char *str, size_t len, byte_writer *writer) */

static bool writeString(const char* str, const size_t len, byte_writer* writer)
{
  /* Write length. */
  if (!writeInt(len, writer))
  {
    return false;
  }

  /* Write actual string. */
  if (write_bytes(str, len, writer) != len)
  {
    return false;
  }

  /* Ok */
  return true;
}

/*}}}  */
/*{{{  static int readString(byte_reader *reader) */

static size_t readString(byte_reader* reader)
{
  size_t len;

  /* Get length of string */
  if (readInt(&len, reader) < 0)
  {
    return ATERM_NON_EXISTING_POSITION;
  }

  /* Assure buffer can hold the string */
  if (text_buffer_size < (len+1))
  {
    text_buffer_size = (len*3)/2;
    text_buffer = (char*) realloc(text_buffer, text_buffer_size);
    if (!text_buffer)
    {
      throw std::runtime_error("out of memory in readString (" + to_string(text_buffer_size) + ")");
    }
  }

  /* Read the actual string */
  if (read_bytes(text_buffer, len, reader) != len)
  {
    return ATERM_NON_EXISTING_POSITION;
  }

  /* Ok, return length of string */
  return len;
}

/*}}}  */

/*{{{  static ATbool write_symbol(function_symbol sym, byte_writer *writer) */

/**
 * Write a symbol to file.
 */

static bool write_symbol(const function_symbol sym, byte_writer* writer)
{
  const char* name = sym.name().c_str();
  if (!writeString(name, strlen(name), writer))
  {
    return false;
  }

  if (!writeInt(sym.arity(), writer))
  {
    return false;
  }

  if (!writeInt(sym.is_quoted(), writer))
  {
    return false;
  }

  return true;
}

/*}}}  */

/*{{{  static sym_entry *get_top_symbol(aterm t) */

/**
 * Retrieve the top symbol of a term. Could be a special symbol
 * (AS_INT, etc) when the term is not an AT_APPL.
 */

static sym_entry* get_top_symbol(const aterm t)
{
  function_symbol sym;

  switch (t.type())
  {
    case AT_INT:
      sym = AS_INT;
      break;
    case AT_LIST:
      sym = (t==aterm_list() ? AS_EMPTY_LIST : AS_LIST);
      break;
    case AT_APPL:
      sym = t.function();
      break;
    default:
      throw std::runtime_error("get_top_symbol: illegal term (" + t.to_string() + ")");
      sym = (function_symbol)-1; // error path...
      break;
  }

  return &sym_entries[function_symbol::at_lookup_table[sym.number()]->index];
}

/*}}}  */
/*{{{  static int bit_width(int val) */

/* How many bits are needed to represent <val> */
static size_t bit_width(size_t val)
{
  size_t nr_bits = 0;

  if (val <= 1)
  {
    return 0;
  }

  while (val)
  {
    val>>=1;
    nr_bits++;
  }

  return nr_bits;
}

/*}}}  */
/*{{{  static void build_arg_tables() */

/**
  * Build argument tables given the fact that the
  * terms have been sorted by symbol.
  */

static void gather_top_symbols(sym_entry* cur_entry,
                               const size_t cur_arg,
                               const size_t total_top_symbols)
{
  size_t index;
  size_t hnr;
  top_symbols_t* tss;
  sym_entry* top_entry;

  tss = &cur_entry->top_symbols[cur_arg];
  tss->nr_symbols = total_top_symbols;
  tss->symbols = std::vector<top_symbol>(total_top_symbols);
  /* tss->symbols = (top_symbol*) calloc(total_top_symbols, sizeof(top_symbol));
  if (!tss->symbols)
  {
    throw std::runtime_error("build_arg_tables: out of memory (top_symbols: " + to_string(total_top_symbols) + ")");
  } */
  tss->toptable_size = (total_top_symbols*5)/4;
  tss->toptable = (top_symbol**) calloc(tss->toptable_size,
                  sizeof(top_symbol*));
  if (!tss->toptable)
  {
    throw std::runtime_error("build_arg_tables: out of memory (table_size: " + to_string(tss->toptable_size) + ")");
  }

  index = 0;
  for (top_entry=first_topsym; top_entry; top_entry=top_entry->next_topsym)
  {
    top_symbol* ts;
    ts = &cur_entry->top_symbols[cur_arg].symbols[index];
    ts->index = top_entry-&sym_entries[0];
    ts->count = top_entry->nr_times_top;
    ts->code_width = bit_width(total_top_symbols);
    ts->code = index;
    ts->s = top_entry->id;

    hnr = ts->s.number() % tss->toptable_size;
    ts->next = tss->toptable[hnr];
    tss->toptable[hnr] = ts;

    top_entry->nr_times_top = 0;
    index++;
  }
}

static void build_arg_tables()
{
  // function_symbol cur_sym;
  size_t cur_trm;
  size_t cur_arg;
  sym_entry* topsym;

  for (size_t cur_sym=0; cur_sym<nr_unique_symbols; cur_sym++)
  {
    sym_entry* cur_entry = &sym_entries[cur_sym];
    size_t arity = cur_entry->arity;

    assert(arity == cur_entry->id.arity());

    /* if (arity == 0)
    {
      cur_entry->top_symbols = NULL;
    }
    else */
    {
      cur_entry->top_symbols = std::vector<top_symbols_t>(arity);
      /* cur_entry->top_symbols = (top_symbols_t*)calloc(arity, sizeof(top_symbols_t));
      if (!cur_entry->top_symbols)
      {
        throw std::runtime_error("build_arg_tables: out of memory (arity: " + to_string(arity) + ")");
      } */
    }

    for (cur_arg=0; cur_arg<arity; cur_arg++)
    {
      size_t total_top_symbols = 0;
      first_topsym = NULL;
      for (cur_trm=0; cur_trm<cur_entry->nr_terms; cur_trm++)
      {
        aterm term = cur_entry->terms[cur_trm].t;
        aterm arg = NULL;
        switch (term.type())
        {
          case AT_LIST:
          {
            aterm_list list = static_cast<aterm_list>(term);
            assert(list!=aterm_list());
            assert(arity == 2);
            if (cur_arg == 0)
            {
              arg = list.head();
            }
            else
            {
              arg = (aterm)(list.tail());
            }
          }
          break;
          case AT_APPL:
            arg = static_cast<aterm_appl>(term)(cur_arg);
            break;
          default:
            throw std::runtime_error("build_arg_tables: illegal term");
            break;
        }
        topsym = get_top_symbol(arg);
        if (!topsym->nr_times_top++)
        {
          total_top_symbols++;
          topsym->next_topsym = first_topsym;
          first_topsym = topsym;
        }
      }

      gather_top_symbols(cur_entry, cur_arg, total_top_symbols);
    }
  }
}

/*}}}  */
/*{{{  static void add_term(sym_entry *entry, aterm t) */

/**
  * Add a term to the termtable of a symbol.
  */
static void add_term(sym_entry* entry, const aterm &t)
{
  size_t hnr = hash_number(&*t,detail::term_size(&*t)) % entry->termtable_size;
  entry->terms[entry->cur_index].t = t;
  entry->terms[entry->cur_index].next = entry->termtable[hnr];
  entry->termtable[hnr] = &entry->terms[entry->cur_index];
  entry->cur_index++;
}

/*}}}  */
/*{{{  static void collect_terms(aterm t) */

/**
 * Collect all terms in the appropriate symbol table.
 */

static void collect_terms(const aterm &t, std::set<aterm> &visited)
{
  function_symbol sym;
  sym_entry* entry;

// ATfprintf(stderr,"COLLECT %t\n",&*t);
  if (visited.count(t)==0)
  {
    switch (t.type())
    {
      case AT_INT:
        sym = AS_INT;
        break;
      case AT_LIST:
      {
        aterm_list list(t);
        if (list==aterm_list())
        {
          sym = AS_EMPTY_LIST;
        }
        else
        {
          sym = AS_LIST;
          collect_terms(list.head(),visited);
          collect_terms((aterm)(list.tail()),visited);
        }
      }
      break;
      case AT_APPL:
      {
        aterm_appl appl(t);

        sym = appl.function();
        const size_t cur_arity = sym.arity();
        for (size_t cur_arg=0; cur_arg<cur_arity; cur_arg++)
        {
          collect_terms(appl(cur_arg),visited);
        }
      }
      break;
      default:
        throw std::runtime_error("collect_terms: illegal term");
        sym = (function_symbol)(-1); // Kill compiler warnings
        break;
    }
    entry = &sym_entries[function_symbol::at_lookup_table[sym.number()]->index];

    assert(entry->id == sym);
    add_term(entry, t);

    visited.insert(t);
  }
}

/*}}}  */
/*{{{  static ATbool write_symbols(byte_writer *writer) */

/**
 * Write all symbols in a term to file.
 */

static bool write_symbols(byte_writer* writer)
{
  size_t sym_idx, arg_idx, top_idx;

  for (sym_idx=0; sym_idx<nr_unique_symbols; sym_idx++)
  {
    sym_entry* cur_sym = &sym_entries[sym_idx];
    if (!write_symbol(cur_sym->id, writer))
    {
      return false;
    }
    if (!writeInt(cur_sym->nr_terms, writer))
    {
      return false;
    }

    for (arg_idx=0; arg_idx<cur_sym->arity; arg_idx++)
    {
      size_t nr_symbols = cur_sym->top_symbols[arg_idx].nr_symbols;
      if (!writeInt(nr_symbols, writer))
      {
        return false;
      }
      for (top_idx=0; top_idx<nr_symbols; top_idx++)
      {
        top_symbol* ts = &cur_sym->top_symbols[arg_idx].symbols[top_idx];
        if (!writeInt(ts->index, writer))
        {
          return false;
        }
      }
    }
  }

  return true;
}

/*}}}  */
/*{{{  static int find_term(sym_entry *entry, aterm t) */

/**
  * Find a term in a sym_entry.
  */

static size_t find_term(sym_entry* entry, const aterm t)
{
  size_t hnr = hash_number(&*t,detail::term_size(&*t)) % entry->termtable_size;
  trm_bucket* cur = entry->termtable[hnr];

  assert(cur);
  while (cur->t != t)
  {
    cur = cur->next;
    assert(cur);
  }

  return cur - entry->terms;
}

/*}}}  */
/*{{{  static top_symbol *find_top_symbol(top_symbols *syms, function_symbol sym) */

/**
 * Find a top symbol in a topsymbol table.
 */

static top_symbol* find_top_symbol(top_symbols_t* syms, const function_symbol sym)
{
  size_t hnr = sym.number() % syms->toptable_size;
  top_symbol* cur = syms->toptable[hnr];

  assert(cur);
  while (cur->s != sym)
  {
    cur = cur->next;
    assert(cur);
  }

  return cur;
}

/*}}}  */
/*{{{  static ATbool write_arg(sym_entry *trm_sym, aterm arg, arg_idx, writer) */

/**
 * Write an argument using a byte_writer.
 */

/* forward declaration */
static bool write_term(const aterm, byte_writer*);

static bool write_arg(sym_entry* trm_sym, const aterm arg, const size_t arg_idx,
                      byte_writer* writer)
{
  top_symbol* ts;
  sym_entry* arg_sym;
  size_t arg_trm_idx;
  function_symbol sym;

  sym = get_top_symbol(arg)->id;
  ts = find_top_symbol(&trm_sym->top_symbols[arg_idx], sym);

  if (writeBits(ts->code, ts->code_width, writer)<0)
  {
    return false;
  }

  arg_sym = &sym_entries[ts->index];

  arg_trm_idx = find_term(arg_sym, arg);
  if (writeBits(arg_trm_idx, arg_sym->term_width, writer)<0)
  {
    return false;
  }

  if (arg_trm_idx >= arg_sym->cur_index &&
      !write_term(arg, writer))
  {
    return false;
  }

  return true;
}

/*}}}  */
/*{{{  static ATbool write_term(aterm t, byte_writer *writer) */

/**
 * Write a term using a writer.
 */

static bool write_term(const aterm t, byte_writer* writer)
{
  size_t arg_idx;
  sym_entry* trm_sym = NULL;
  {
    switch (t.type())
    {
      case AT_INT:
        /* If aterm integers are > 32 bits, then this can fail. */
        if (writeBits(aterm_int(t).value(), INT_SIZE_IN_BAF, writer) < 0)
        {
          return false;
        }
        trm_sym = &sym_entries[function_symbol::at_lookup_table[AS_INT.number()]->index];
        break;
      case AT_LIST:
      {
        aterm_list list (t);
        if (list==aterm_list())
        {
          trm_sym = &sym_entries[function_symbol::at_lookup_table[AS_EMPTY_LIST.number()]->index];
        }
        else
        {
          trm_sym = &sym_entries[function_symbol::at_lookup_table[AS_LIST.number()]->index];
          if (!write_arg(trm_sym, list.head(), 0, writer))
          {
            return false;
          }
          if (!write_arg(trm_sym, (aterm)(list.tail()), 1, writer))
          {
            return false;
          }
        }
      }
      break;
      case AT_APPL:
      {
        size_t arity;
        function_symbol sym = t.function();
        trm_sym = &sym_entries[function_symbol::at_lookup_table[sym.number()]->index];
        assert(sym == trm_sym->id);
        arity = sym.arity();
        for (arg_idx=0; arg_idx<arity; arg_idx++)
        {
          aterm cur_arg = static_cast<aterm_appl>(t)(arg_idx);
          if (!write_arg(trm_sym, cur_arg, arg_idx, writer))
          {
            return false;
          }
        }
      }
      break;
      default:
        throw std::runtime_error("write_term: illegal term");
        break;
    }
  }
  if (trm_sym->terms[trm_sym->cur_index].t != t)
  {
    throw std::runtime_error("terms out of sync at pos " + to_string(trm_sym->cur_index) + " of sym " + ATwriteAFunToString(trm_sym->id) +
                             ", term in table was " + (trm_sym->terms[trm_sym->cur_index].t).to_string() + ", expected " + t.to_string());
  }
  trm_sym->cur_index++;

  return true;
}

/*}}}  */

/*{{{  static void free_write_space() */

/**
 * Free all space allocated by the bafio write functions.
 */

static void free_write_space()
{
  size_t i, j;

  for (i=0; i<nr_unique_symbols; i++)
  {
    sym_entry* entry = &sym_entries[i];

    free(entry->terms);
    entry->terms = NULL;
    free(entry->termtable);
    entry->termtable = NULL;

    for (j=0; j<entry->arity; j++)
    {
      top_symbols_t* topsyms = &entry->top_symbols[j];
      /* if (topsyms->symbols)
      {
        free(topsyms->symbols);
        topsyms->symbols = NULL;
      } */
      topsyms->symbols=std::vector<top_symbol>();
      if (topsyms->toptable)
      {
        free(topsyms->toptable);
        topsyms->toptable = NULL;
      }
      /*free(topsyms);*/
    }

    /* if (entry->top_symbols)
    {
      free(entry->top_symbols);
      entry->top_symbols = NULL;
    } */
    entry->top_symbols=std::vector<top_symbols_t>();
  }
  sym_entries=std::vector<sym_entry>();

  // sym_entries = NULL;
}

/*}}}  */
/*{{{  ATbool write_baf(aterm t, byte_writer *writer) */

static bool
write_baf(const aterm &t, byte_writer* writer)
{
  size_t nr_unique_terms = 0;
  size_t nr_symbols = function_symbol::at_lookup_table.size();
  size_t cur;

  /* Initialize bit buffer */
  bit_buffer     = '\0';
  bits_in_buffer = 0; /* how many bits in bit_buffer are used */

  for (size_t lcv=0; lcv<nr_symbols; lcv++)
  {
    if (function_symbol::at_lookup_table[lcv]->reference_count>0)
    {
      function_symbol::at_lookup_table[lcv]->count = 0;
    }
  }
  nr_unique_symbols = AT_calcUniqueAFuns(t);

  sym_entries = std::vector<sym_entry>(nr_unique_symbols);
  /* sym_entries = (sym_entry*) calloc(nr_unique_symbols, sizeof(sym_entry));
  if (!sym_entries)
  {
    std::runtime_error("write_baf: out of memory (" + to_string(nr_unique_symbols) + " unique symbols!");
  } */

  /*{{{  Collect all unique symbols in the input term */

  for (size_t lcv=cur=0; lcv<nr_symbols; lcv++)
  {
    _SymEntry* entry = function_symbol::at_lookup_table[lcv];
    if (entry->reference_count>0 && entry->count>0)
    {
      assert(lcv == entry->id);
      nr_unique_terms += entry->count;

      sym_entries[cur].term_width = bit_width(entry->count);
      sym_entries[cur].id = lcv;
      sym_entries[cur].arity = function_symbol(lcv).arity();
      sym_entries[cur].nr_terms = entry->count;
      sym_entries[cur].terms = (trm_bucket*) calloc(entry->count,
                               sizeof(trm_bucket));
      if (!sym_entries[cur].terms)
      {
        std::runtime_error("write_baf: out of memory (sym: " + ATwriteAFunToString(lcv) + ", terms: " + to_string(entry->count) + ")");
      }
      sym_entries[cur].termtable_size = (entry->count*5)/4;
      sym_entries[cur].termtable =
        (trm_bucket**) calloc(sym_entries[cur].termtable_size,
                                 sizeof(trm_bucket*));
      if (!sym_entries[cur].termtable)
      {
        std::runtime_error("write_baf: out of memory (termtable_size: " + to_string(sym_entries[cur].termtable_size) + ")");
      }

      entry->index = cur;
      entry->count = 0; /* restore invariant that symbolcount is zero */

      cur++;
    }
  }

  assert(cur == nr_unique_symbols);

  /*}}}  */

  std::set<aterm> visited;
  collect_terms(t,visited);
  // AT_unmarkIfAllMarked(t);

  /* reset cur_index */
  for (size_t lcv=0; lcv < nr_unique_symbols; lcv++)
  {
    sym_entries[lcv].cur_index = 0;
  }

  build_arg_tables();
  /*print_sym_entries();*/

  /*{{{  write header */

  if (!writeInt(0, writer))
  {
    return false;
  }

  if (!writeInt(BAF_MAGIC, writer))
  {
    return false;
  }

  if (!writeInt(BAF_VERSION, writer))
  {
    return false;
  }

  if (!writeInt(nr_unique_symbols, writer))
  {
    return false;
  }

  if (!writeInt(nr_unique_terms, writer))
  {
    return false;
  }

  /*}}}  */

  if (!write_symbols(writer))
  {
    return false;
  }

  /* Write the top symbol */
  if (!writeInt(get_top_symbol(t)-&sym_entries[0], writer))
  {
    return false;
  }

  if (!write_term(t, writer))
  {
    return false;
  }

  if (flushBitsToWriter(writer)<0)
  {
    return false;
  }

  free_write_space();

  return true;
}

/*}}}  */

/*{{{  char *ATwriteToBinaryString(aterm t, int *len) */

unsigned char* ATwriteToBinaryString(const aterm &t, size_t* len)
{
  static byte_writer writer;
  static bool initialized = false;

  if (!initialized)
  {
    writer.type = STRING_WRITER;
    writer.u.string_data.buf = (unsigned char*)calloc(BUFSIZ, 1);
    writer.u.string_data.max_size = BUFSIZ;
    initialized = true;
  }
  writer.u.string_data.cur_size = 0;

  if (!write_baf(t, &writer))
  {
    return NULL;
  }

  if (len != NULL)
  {
    *len = writer.u.string_data.cur_size;
  }

  return writer.u.string_data.buf;
}

/*}}}  */
/*{{{  ATbool ATwriteToBinaryFile(aterm t, FILE *file) */

bool ATwriteToBinaryFile(const aterm &t, FILE* file)
{
  static byte_writer writer;
  static bool initialized = false;

  if (!initialized)
  {
    writer.type = FILE_WRITER;
    initialized = true;
  }
  writer.u.file_data = file;

#ifdef WIN32
  if (_setmode(_fileno(file), _O_BINARY) == -1)
  {
    perror("Warning: Cannot set outputfile to binary mode.");
  }
#endif

  return write_baf(t, &writer);
}

/*}}}  */

/*{{{  aterm ATwriteToNamedBinaryFile(char *name) */

/**
  * Write an aterm to a named BAF file
  */

bool ATwriteToNamedBinaryFile(aterm t, const char* name)
{
  FILE*  f;
  bool result;

  if (!strcmp(name, "-"))
  {
    return ATwriteToBinaryFile(t, stdout);
  }

  if (!(f = fopen(name, "wb")))
  {
    return false;
  }

  result = ATwriteToBinaryFile(t, f);
  fclose(f);

  return result;
}

/*}}}  */

/*{{{  function_symbol read_symbol(byte_reader *reader) */

/**
  * Read a single symbol from file.
  */

static function_symbol read_symbol(byte_reader* reader)
{
  size_t arity, quoted;
  size_t len;

  if ((len = readString(reader)) == ATERM_NON_EXISTING_POSITION)
  {
    return ATERM_NON_EXISTING_POSITION;
  }

  text_buffer[len] = '\0';

  if (readInt(&arity, reader) < 0)
  {
    return ATERM_NON_EXISTING_POSITION;
  }

  if (readInt(&quoted, reader) < 0)
  {
    return ATERM_NON_EXISTING_POSITION;
  }

  return function_symbol(text_buffer, arity, quoted ? true : false);
}

/*}}}  */

/*{{{  ATbool read_all_symbols(byte_reader *reader) */

/**
 * Read all symbols from file.
 */

static bool read_all_symbols(byte_reader* reader)
{
  size_t k, val;
  size_t i, j, arity;

  for (i=0; i<nr_unique_symbols; i++)
  {
    /*{{{  Read the actual symbol */

    function_symbol sym = read_symbol(reader);
    if (sym == (function_symbol)(-1))
    {
      std::runtime_error("read_symbols: error reading symbol, giving up.");
    }

    read_symbols[i].sym = sym;
    arity = sym.arity();
    read_symbols[i].arity = arity;

    /*}}}  */
    /*{{{  Read term count and allocate space */

    if (readInt(&val, reader) < 0 || val == 0)
    {
      return false;
    }
    read_symbols[i].nr_terms = val;
    read_symbols[i].term_width = bit_width(val);
    if (val == 0)
    {
      assert(0);
      // read_symbols[i].terms = NULL;
    }
    else
    {
      read_symbols[i].terms = std::vector<aterm>(val);
    }
    /* if (!read_symbols[i].terms)
    {
      std::runtime_error("read_symbols: could not allocate space for " + to_string(val) + " terms.");
    } */

    /*}}}  */

    /*{{{  Allocate space for topsymbol information */

    if (arity == 0)
    {
      read_symbols[i].nr_topsyms = NULL;
      read_symbols[i].sym_width = NULL;
      read_symbols[i].topsyms = NULL;
    }
    else
    {
      read_symbols[i].nr_topsyms = (size_t*)calloc(arity, sizeof(size_t));
      if (!read_symbols[i].nr_topsyms)
        std::runtime_error("read_all_symbols: out of memory trying to allocate "
                           "space for " + to_string(arity) + " arguments.");

      read_symbols[i].sym_width = (size_t*)calloc(arity, sizeof(size_t));
      if (!read_symbols[i].sym_width)
        std::runtime_error("read_all_symbols: out of memory trying to allocate "
                           "space for " + to_string(arity) + " arguments.");

      read_symbols[i].topsyms = (size_t**)calloc(arity, sizeof(size_t*));
      if (!read_symbols[i].topsyms)
        std::runtime_error("read_all_symbols: out of memory trying to allocate "
                           "space for " + to_string(arity) + " arguments.");
    }

    /*}}}  */

    for (j=0; j<read_symbols[i].arity; j++)
    {
      if (readInt(&val, reader) < 0)
      {
        return false;
      }

      read_symbols[i].nr_topsyms[j] = val;
      read_symbols[i].sym_width[j] = bit_width(val);
      read_symbols[i].topsyms[j] = (size_t*)calloc(val, sizeof(size_t));
      if (!read_symbols[i].topsyms[j])
      {
        std::runtime_error("read_symbols: could not allocate space for " + to_string(val) + " top symbols.");
      }

      for (k=0; k<read_symbols[i].nr_topsyms[j]; k++)
      {
        if (readInt(&val, reader) < 0)
        {
          return false;
        }
        read_symbols[i].topsyms[j][k] = val;
      }
    }

  }

  return true;
}

/*}}}  */
/*{{{  aterm read_term(sym_read_entry *sym, byte_reader *reader) */

static aterm read_term(sym_read_entry* sym, byte_reader* reader)
{
  size_t val;
  size_t i, arity = sym->arity;
  sym_read_entry* arg_sym;
  // aterm stack_args[MAX_STACK_ARGS];
  std::vector<aterm> args(arity);
  aterm result;

  for (i=0; i<arity; i++)
  {
    if (readBits(&val, sym->sym_width[i], reader) < 0)
    {
      return NULL;
    }
    if (val >= sym->nr_topsyms[i])
    {
      return NULL;
    }
    arg_sym = &read_symbols[sym->topsyms[i][val]];

    if (readBits(&val, arg_sym->term_width, reader) < 0)
    {
      return NULL;
    }

    if (val >= arg_sym->nr_terms)
    {
      return NULL;
    }
    if (!&*arg_sym->terms[val])
    {
      arg_sym->terms[val] = read_term(arg_sym, reader);
      if (!&*arg_sym->terms[val])
      {
        return NULL;
      }
    }

    args[i] = arg_sym->terms[val];
  }

  if (sym->sym==AS_INT)
  {
    /*{{{  Read an integer */

    if (readBits(&val, INT_SIZE_IN_BAF, reader) < 0)
    {
      return NULL;
    }

    result = aterm_int((int)val);

      /*}}}  */
  }
  else if (sym->sym==AS_LIST)
  {
      result = push_front((aterm_list)args[1], args[0]);
  }
  else if (sym->sym==AS_EMPTY_LIST)
  {
    result = aterm_list();
  }
  else
  {
    /* Must be a function application */
    result = aterm_appl(sym->sym, args.begin(),args.end());
  }

  return result;
}

/*}}}  */

/*{{{  static void free_read_space() */

/**
 * Free all temporary space allocated by the baf read functions.
 */

static void free_read_space()
{
  size_t i, j;

  for (i=0; i<nr_unique_symbols; i++)
  {
    sym_read_entry* entry = &read_symbols[i];

    // if (entry->terms)
    // {
    //   delete &entry->terms;
    // }
    if (entry->nr_topsyms)
    {
      free(entry->nr_topsyms);
    }
    if (entry->sym_width)
    {
      free(entry->sym_width);
    }

    for (j=0; j<entry->arity; j++)
    {
      free(entry->topsyms[j]);
    }
    if (entry->topsyms)
    {
      free(entry->topsyms);
    }

  }
  read_symbols=std::vector<sym_read_entry>(); // Release memory, and prevent read symbols to be 
                                              // destructed after the destruction of function_symbols, which leads
                                              // to decreasing reference counters, after at_lookup_table has
                                              // been destroyed (i.e. core dump).
}

/*}}}  */

/*{{{  aterm read_baf(byte_reader *reader) */

/**
 * Read a term from a BAF reader.
 */

static
aterm read_baf(byte_reader* reader)
{
  size_t val, nr_unique_terms;
  aterm result = NULL;

  /* Initialize bit buffer */
  bit_buffer     = '\0';
  bits_in_buffer = 0; /* how many bits in bit_buffer are used */

  /*{{{  Read header */

  if (readInt(&val, reader) < 0)
  {
    return NULL;
  }

  if (val == 0)
  {
    if (readInt(&val, reader) < 0)
    {
      return NULL;
    }
  }

  if (val != BAF_MAGIC)
  {
    mCRL2log(mcrl2::log::error) << "read_baf: input is not in BAF!" << std::endl;
    return NULL;
  }

  if (readInt(&val, reader) < 0)
  {
    return NULL;
  }

  if (val != BAF_VERSION)
  {
    mCRL2log(mcrl2::log::error) << "read_baf: wrong BAF version, giving up!" << std::endl;
    return NULL;
  }

  if (readInt(&val, reader) < 0)
  {
    return NULL;
  }
  nr_unique_symbols = val;

  if (readInt(&nr_unique_terms, reader) < 0)
  {
    return NULL;
  }

  /*}}}  */
  /*{{{  Allocate symbol space */

  read_symbols = std::vector<sym_read_entry>(nr_unique_symbols);
  /* read_symbols = (sym_read_entry*)calloc(nr_unique_symbols, sizeof(sym_read_entry));
  if (!read_symbols)
  {
    std::runtime_error("read_baf: out of memory when allocating " + to_string(nr_unique_symbols) + " syms.");
  } */

  /*}}}  */

  if (!read_all_symbols(reader))
  {
    return NULL;
  }

  if (readInt(&val, reader) < 0)
  {
    return NULL;
  }

  result = read_term(&read_symbols[val], reader);

  free_read_space();

  return result;
}

/*}}}  */

/*{{{  aterm ATreadFromBinaryString(const unsigned char *s, int size) */

aterm ATreadFromBinaryString(const unsigned char* s, size_t size)
{
  byte_reader reader;

  init_string_reader(&reader, s, size);

  return read_baf(&reader);
}

/*}}}  */
/*{{{  aterm ATreadFromBinaryFile(FILE *file) */

aterm ATreadFromBinaryFile(FILE* file)
{
  byte_reader reader;

  init_file_reader(&reader, file);

#ifdef WIN32
  if (_setmode(_fileno(file), _O_BINARY) == -1)
  {
    perror("Warning: Cannot set inputfile to binary mode."
          );
  }
#endif

  return read_baf(&reader);
}

/*}}}  */

} // namespace atermpp
