/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "smt2_parser.h"

#include <istream>
#include <ostream>

bool smt2_tokenizert::is_simple_symbol_character(char ch)
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  return isalnum(ch) ||
     ch=='~' || ch=='!' || ch=='@' || ch=='$' || ch=='%' ||
     ch=='^' || ch=='&' || ch=='*' || ch=='_' || ch=='-' ||
     ch=='+' || ch=='=' || ch=='<' || ch=='>' || ch=='.' ||
     ch=='?' || ch=='/';
}

smt2_tokenizert::tokent smt2_tokenizert::get_simple_symbol()
{
  // any non-empty sequence of letters, digits and the characters
  // ~ ! @ $ % ^ & * _ - + = < > . ? /
  // that does not start with a digit and is not a reserved word.

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(is_simple_symbol_character(ch))
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return SYMBOL;
    }
  }

  // eof -- this is ok here
  return END_OF_FILE;
}

smt2_tokenizert::tokent smt2_tokenizert::get_decimal_numeral()
{
  // we accept any sequence of digits and dots

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(isdigit(ch) || ch=='.')
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  return END_OF_FILE;
}

smt2_tokenizert::tokent smt2_tokenizert::get_bin_numeral()
{
  // we accept any sequence of '0' or '1'

  buffer.clear();
  buffer+='#';
  buffer+='b';

  char ch;
  while(in.get(ch))
  {
    if(ch=='0' || ch=='1')
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  return END_OF_FILE;
}

smt2_tokenizert::tokent smt2_tokenizert::get_hex_numeral()
{
  // we accept any sequence of '0'-'9', 'a'-'f', 'A'-'F'

  buffer.clear();
  buffer+='#';
  buffer+='x';

  char ch;
  while(in.get(ch))
  {
    if(isxdigit(ch))
    {
      buffer+=ch;
    }
    else
    {
      in.unget(); // put back
      return NUMERAL;
    }
  }

  // eof -- this is ok here
  return END_OF_FILE;
}

smt2_tokenizert::tokent smt2_tokenizert::get_quoted_symbol()
{
  // any sequence of printable ASCII characters (including space,
  // tab, and line-breaking characters) except for the backslash
  // character \, that starts and ends with | and does not otherwise
  // contain |

  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(ch=='|')
      return SYMBOL; // done
    buffer+=ch;
  }

  // Hmpf. Eof before end of quoted string. This is an error.
  return ERROR;
}

smt2_tokenizert::tokent smt2_tokenizert::get_string_literal()
{
  buffer.clear();

  char ch;
  while(in.get(ch))
  {
    if(ch=='"')
    {
      // quotes may be escaped by repeating
      if(in.get(ch))
      {
        if(ch=='"')
        {
        }
        else
        {
          in.unget();
          return STRING_LITERAL; // done
        }
      }
      else
        return STRING_LITERAL; // done
    }
    buffer+=ch;
  }

  // Hmpf. Eof before end of string literal. This is an error.
  ok=false;
  error("EOF within string literal");
  return ERROR;
}

smt2_tokenizert::tokent smt2_tokenizert::next_token()
{
  if(peeked)
    return peeked=false, token;

  char ch;

  while(in.get(ch))
  {
    switch(ch)
    {
    case ' ':
    case '\n':
    case '\r':
    case '\t':
    case static_cast<char>(160): // non-breaking space
      // skip any whitespace
      break;

    case ';': // comment
      // skip until newline
      while(in.get(ch) && ch!='\n')
      {
        // ignore
      }
      break;

    case '(':
      // produce sub-expression
      return token=OPEN;

    case ')':
      // done with sub-expression
      return token=CLOSE;

    case '|': // quoted symbol
      return token=get_quoted_symbol();

    case '"': // string literal
      return token=get_string_literal();

    case ':': // keyword
      return token=get_simple_symbol();

    case '#':
      if(in.get(ch))
      {
        if(ch=='b')
          return token=get_bin_numeral();
        else if(ch=='x')
          return token=get_hex_numeral();
        else
        {
          ok=false;
          error("unknown numeral token");
          return token=ERROR;
        }
      }
      else
      {
        ok=false;
        error("unexpected EOF in numeral token");
        return token=ERROR;
      }
      break;

    default: // likely a simple symbol or a numeral
      if(isdigit(ch))
      {
        in.unget();
        return token=get_decimal_numeral();
      }
      else if(is_simple_symbol_character(ch))
      {
        in.unget();
        return token=get_simple_symbol();
      }
      else
      {
        // illegal character, error
        ok=false;
        error("unexpected character");
        return token=ERROR;
      }
    }
  }

  return token=END_OF_FILE;
}

void new_smt2_parsert::command_sequence()
{
  while(next_token()==OPEN)
  {
    if(next_token()!=SYMBOL)
    {
      ok=false;
      error("expected symbol as command");
      return;
    }

    command(buffer);

    switch(next_token())
    {
    case END_OF_FILE:
      ok=false;
      error("expected closing parenthesis at end of command, but got EOF");
      return;

    case CLOSE:
      // what we expect
      break;

    default:
      ok=false;
      error("expected end of command");
      return;
    }
  }

  if(token!=END_OF_FILE)
  {
    ok=false;
    error("unexpected token: "+buffer);
  }
}

void new_smt2_parsert::ignore_command()
{
  std::size_t parentheses=0;
  while(true)
  {
    switch(peek())
    {
    case OPEN:
      next_token();
      parentheses++;
      break;

    case CLOSE:
      if(parentheses==0)
        return; // done

      next_token();
      parentheses--;
      break;

    case END_OF_FILE:
      ok=false;
      error("unexpected EOF in command");
      return;

    default:
      next_token();
    }
  }
}
