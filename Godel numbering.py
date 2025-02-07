#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
An OOP implementation for encoding and decoding Gödel numbers
"""

import re
import panda
import collections
from itertools import groupby, takewhile
from math import sqrt
from re import Scanner

def prod(iterable):
  """
  Returns the product of the elements of iterable.
  """
  product = 1
  for n in iterable:
    product *= n
  return product

def sieve(n):
  """
  Returns all primes smaller than the argument "n".
  """
  if n < 2: return []  

  lng = int((n / 2) - 1 + n % 2)  ## Remove even numbers.
  sieve = [True] * (lng + 1)  

  for i in range(int(sqrt(n)) >> 1):  
    if not sieve[i]: continue
    ## Unmark all multiples of i, starting at i**2  
    for j in range( (i * (i + 3) << 1) + 3, lng, (i << 1) + 3):  
      sieve[j] = False

  primes = [2] + [(i << 1) + 3 for i in range(lng) if sieve[i]]
  return primes


def factor(n):
  """
  Returns an array of the prime factors of the argument "n" from smallest
  to largest.
  """
  factor = 2
  factors = []
  while factor <= n:
    if n % factor == 0:
      n //= factor
      factors.append(factor)
    else:
      factor += 1
  return factors


Bijection = collections.namedtuple("Bijection", ["mapping", "inverse"])

def create_bijection(mapping):
    """
    Given a one-to-one mapping (dictionary), return a Bijection named tuple with
    attributes 'mapping' and 'inverse'.

    Raises:
        ValueError: If the mapping is not one-to-one.
    """
    inverse = {}
    for k, v in mapping.items():
        if v in inverse:
            raise ValueError("duplicate key '{}' found".format(v))
        inverse[v] = k
    return Bijection(mapping=mapping.copy(), inverse=inverse)


# --- Lexer ---

class LexicalException(Exception):
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return repr(self.message)


class Lexer:
    """
    A simple lexer built upon regular-expression scanning.
    It tokenizes the input string into four types:
      - CONSTANT_TYPE: constant signs (e.g. ~, ∨, ⊃, ∃, =, 0, s, (, ), ,, +, ×)
      - NUMERICAL_TYPE: numerical variables (e.g. x, y, z, possibly with tick marks)
      - SENTENTIAL_TYPE: sentential variables (e.g. p, q, r, possibly with tick marks)
      - PREDICATE_TYPE: predicate variables (e.g. P, Q, R, possibly with tick marks)
    """
    CONSTANT_TYPE = "C"
    NUMERICAL_TYPE = "N"
    SENTENTIAL_TYPE = "S"
    PREDICATE_TYPE = "P"

    def __init__(self, tick, numerical_vars, sentential_vars, predicate_vars, constant_signs):
        self.tick = tick
        self.numerical_vars = numerical_vars
        self.sentential_vars = sentential_vars
        self.predicate_vars = predicate_vars
        # Build regex patterns.
        self.constant_pattern = self._match_any(constant_signs.mapping.keys())
        self.numerical_pattern = self._match_any_with_ticks(numerical_vars)
        self.sentential_pattern = self._match_any_with_ticks(sentential_vars)
        self.predicate_pattern = self._match_any_with_ticks(predicate_vars)

    def _match_any(self, iterable):
        """Return a regex pattern matching any character in iterable."""
        return "[{}]".format("".join(iterable))

    def _match_any_with_ticks(self, iterable):
        """
        Return a regex pattern matching any character in iterable,
        possibly followed by zero or more tick marks.
        """
        return "{}{}*".format(self._match_any(iterable), self.tick)

    def scan(self, string):
        """
        Scans the input string and returns a list of tokens.
        Each token is a pair (token_type, lexeme).
        """
        scanner = re.Scanner([
            (self.constant_pattern, lambda scanner, token: (Lexer.CONSTANT_TYPE, token)),
            (self.numerical_pattern, lambda scanner, token: (Lexer.NUMERICAL_TYPE, token)),
            (self.sentential_pattern, lambda scanner, token: (Lexer.SENTENTIAL_TYPE, token)),
            (self.predicate_pattern, lambda scanner, token: (Lexer.PREDICATE_TYPE, token))
        ])
        tokens, remainder = scanner.scan(string)
        if remainder:
            snippet = remainder[:10]
            raise LexicalException("Error lexing input near {}...".format(snippet))
        return tokens


# --- Gödel Encoder/Decoder ---

class GodelEncoder:
    """
    Encapsulates the encoding and decoding of expressions (from PM)
    as Gödel numbers.

    Configuration parameters (with defaults) include:
      - upperbound: upper bound on primes (affects startup time and expressivity)
      - tick: the character used to “tick” a variable (e.g. x, x`, x``, ...)
      - numerical_vars: pool for numerical variables (default: x, y, z)
      - sentential_vars: pool for sentential variables (default: p, q, r)
      - predicate_vars: pool for predicate variables (default: P, Q, R)
      - constant_signs: a mapping for constant symbols.
    """
    def __init__(self, upperbound=10000, tick='`',
                 numerical_vars=('x', 'y', 'z'),
                 sentential_vars=('p', 'q', 'r'),
                 predicate_vars=('P', 'Q', 'R'),
                 constant_signs=None):
        if constant_signs is None:
            constant_signs = {
                '~': 1,
                '∨': 2,
                '⊃': 3,
                '∃': 4,
                '=': 5,
                '0': 6,
                's': 7,
                '(': 8,
                ')': 9,
                ',': 10,
                '+': 11,
                '×': 12
            }
        self.tick = tick
        self.numerical_vars = numerical_vars
        self.sentential_vars = sentential_vars
        self.predicate_vars = predicate_vars
        # Use the function-based bijection.
        self.constant_signs = create_bijection(constant_signs)

        self.upperbound = upperbound
        self.prime = sieve(upperbound)
        max_const = max(self.constant_signs.mapping.values())
        self.prime_offset = len(list(takewhile(lambda x: x < max_const, self.prime)))
        self.lexer = Lexer(tick, numerical_vars, sentential_vars, predicate_vars,
                             self.constant_signs)

    class _EncodeState:
        """
        Holds the state while encoding an expression.
        Keeps track of which variable tokens have already been assigned a number.
        """
        def __init__(self, encoder):
            self.encoder = encoder
            self.encoding = []         # List of numbers corresponding to tokens.
            self.numerical_map = {}    # Maps a numerical variable (str) to its number.
            self.sentential_map = {}   # Maps a sentential variable (str) to its number.
            self.predicate_map = {}    # Maps a predicate variable (str) to its number.

        def encode_constant(self, symbol):
            return self.encoder.constant_signs.mapping[symbol]

        def encode_numerical(self, symbol):
            if symbol in self.numerical_map:
                return self.numerical_map[symbol]
            idx = len(self.numerical_map)
            gnum = self.encoder.prime[self.encoder.prime_offset + idx]
            self.numerical_map[symbol] = gnum
            return gnum

        def encode_sentential(self, symbol):
            if symbol in self.sentential_map:
                return self.sentential_map[symbol]
            idx = len(self.sentential_map)
            gnum = self.encoder.prime[self.encoder.prime_offset + idx] ** 2
            self.sentential_map[symbol] = gnum
            return gnum

        def encode_predicate(self, symbol):
            if symbol in self.predicate_map:
                return self.predicate_map[symbol]
            idx = len(self.predicate_map)
            gnum = self.encoder.prime[self.encoder.prime_offset + idx] ** 3
            self.predicate_map[symbol] = gnum
            return gnum

    class _DecodeState:
        """
        Holds the state while decoding a Gödel number.
        It “assigns” variable names (possibly with ticks) to numbers as needed.
        """
        def __init__(self, encoder):
            self.encoder = encoder
            self.numerical_map = {}   # Maps number to numerical variable (str).
            self.sentential_map = {}  # Maps number to sentential variable (str).
            self.predicate_map = {}   # Maps number to predicate variable (str).

        def _next_var_name(self, assigned, pool):
            count = len(assigned)
            ticks = count // len(pool)
            return pool[count % len(pool)] + self.encoder.tick * ticks

        def decode_numerical(self, gnum):
            if gnum in self.numerical_map:
                return self.numerical_map[gnum]
            symbol = self._next_var_name(self.numerical_map, self.encoder.numerical_vars)
            self.numerical_map[gnum] = symbol
            return symbol

        def decode_sentential(self, gnum):
            if gnum in self.sentential_map:
                return self.sentential_map[gnum]
            symbol = self._next_var_name(self.sentential_map, self.encoder.sentential_vars)
            self.sentential_map[gnum] = symbol
            return symbol

        def decode_predicate(self, gnum):
            if gnum in self.predicate_map:
                return self.predicate_map[gnum]
            symbol = self._next_var_name(self.predicate_map, self.encoder.predicate_vars)
            self.predicate_map[gnum] = symbol
            return symbol

    def encode(self, string):
        """
        Encode a string (an expression from the formal system PM)
        as a Gödel number.
        """
        if not string:
            return 0

        state = GodelEncoder._EncodeState(self)
        tokens = self.lexer.scan(string)

        for token_type, lexeme in tokens:
            if token_type == Lexer.CONSTANT_TYPE:
                gnum = state.encode_constant(lexeme)
            elif token_type == Lexer.NUMERICAL_TYPE:
                gnum = state.encode_numerical(lexeme)
            elif token_type == Lexer.SENTENTIAL_TYPE:
                gnum = state.encode_sentential(lexeme)
            elif token_type == Lexer.PREDICATE_TYPE:
                gnum = state.encode_predicate(lexeme)
            else:
                raise ValueError("Unknown token type: {}".format(token_type))
            state.encoding.append(gnum)

        # The Gödel number is the product of primes raised to the encoded exponents.
        return prod(self.prime[i] ** g for i, g in enumerate(state.encoding))

    def decode(self, number):
        """
        Decode a Gödel number back into a string of the formal system PM.
        """
        if not number:
            return ""

        state = GodelEncoder._DecodeState(self)
        symbols = []

        # Factor the number and group by prime factors.
        factor_groups = (
            (prime, sum(1 for _ in group))
            for prime, group in groupby(factor(number))
        )
        for i, (prime_factor, exponent) in enumerate(factor_groups):
            if self.prime[i] != prime_factor:
                raise ValueError(
                    "Not a Gödel number: prime at index {} is {} but should be {}."
                    .format(i, prime_factor, self.prime[i])
                )

            gnum = exponent
            # First, try to decode a constant sign.
            const = self.constant_signs.inverse.get(gnum)
            if const is not None:
                symbols.append(const)
            else:
                # If gnum is itself a prime, assume a numerical variable.
                if gnum in self.prime:
                    symbols.append(state.decode_numerical(gnum))
                else:
                    # Otherwise, factor gnum. A sentential variable is encoded as a prime squared,
                    # and a predicate variable as a prime cubed.
                    subfactors = factor(gnum)
                    if len(set(subfactors)) != 1:
                        raise ValueError("{} is not prime, a prime squared, or a prime cubed."
                                         .format(gnum))
                    if len(subfactors) == 2 and subfactors[0] in self.prime:
                        symbols.append(state.decode_sentential(gnum))
                    elif len(subfactors) == 3 and subfactors[0] in self.prime:
                        symbols.append(state.decode_predicate(gnum))
                    else:
                        raise ValueError("{} is not prime, a prime squared, or a prime cubed."
                                         .format(gnum))
        return "".join(symbols)


# --- Example Usage ---

if __name__ == '__main__':
    test_string1 = '0=0'
    test_string2 = '(∃pPx)(x=sy)'

    coder = GodelEncoder()
    encoded1 = coder.encode(test_string1)
    encoded2 = coder.encode(test_string2)

    print("Encoded values:")
    print(encoded1)
    print(encoded2)

    decoded1 = coder.decode(encoded1)
    decoded2 = coder.decode(encoded2)

    print("\n(Original, Encoded, Decoded)")
    print((test_string1, encoded1, decoded1))
    print((test_string2, encoded2, decoded2))