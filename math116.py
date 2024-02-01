#!/usr/bin/env python3
# coding: utf-8

from itertools import cycle
from collections import Counter
import re

ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


### Tools for primitive ciphers (Caesar, Vigenère, etc) ###

DELETECHARS = re.compile(r"[^A-Z]")
def cleanstring(string):
    "Converts a string to uppercase and removes any non-letter characters"
    return DELETECHARS.sub("", string.upper())

def tonum(char):
    "Converts a letter of the alphabet into a number in the range 0..25"
    return ord(char) - 65

def tochar(num):
    "Converts a number in the range 0..25 into a letter of the alphabet"
    return chr(num + 65)

def caesar_encrypt(text, key):
    "Encrypts with the Caesar cipher, using the single letter 'key' as the key"
    return "".join(tochar((tonum(c) + key) % 26) for c in text)

def caesar_decrypt(text, key):
    "Decrypts with the Caesar cipher, using the single letter 'key' as the key"
    return caesar_encrypt(text, -key)

def affine_encrypt(plaintext, a, b):
    "Encrypts 'plaintext' with the affine cipher E(m) = a*m + b (mod 26)"
    return "".join(tochar((a * tonum(c) + b) % 26) for c in plaintext)

def affine_decrypt(ciphertext, a, b):
    "Decrypts 'ciphertext' with the affine cipher E(m) = a*m + b (mod 26)"
    d = inverse(a, 26)
    return affine_encrypt(ciphertext, d, -b*d)
    # or return "".join(tochar((tonum(c) - b) * d % 26) for c in plaintext)

def vigenere_encrypt(text, key):
    "Encrypts with the Vigenère cipher, using 'key' as the key word"
    key = [tonum(c) for c in key]
    return "".join(tochar((tonum(c) + k) % 26) for c, k in zip(text, cycle(key)))

def vigenere_decrypt(text, key):
    "Decrypts with the Vigenère cipher, using 'key' as the key word"
    key = [tonum(c) for c in key]
    return "".join(tochar((tonum(c) - k) % 26) for c, k in zip(text, cycle(key)))

# The following constants are used by the viegenere_crack function. 
LETTER_FREQUENCIES = (
    0.082, 0.015, 0.028, 0.043, 0.127, 0.022, 0.020, 0.061, 0.070, 
    0.002, 0.008, 0.040, 0.024, 0.067, 0.075, 0.019, 0.001, 0.060, 
    0.063, 0.091, 0.028, 0.010, 0.023, 0.001, 0.020, 0.001, 
)

SHIFTED_FREQUENCIES = [
    LETTER_FREQUENCIES[-i:] + LETTER_FREQUENCIES[:-i] for i in range(26)
]

def dot_product(list1, list2):
    return sum(a*b for a, b in zip(list1, list2))

def vigenere_crack(ciphertext, maxkeylength=None):
    """Attempt to decrypt a ciphertext encrypted with the Vigenère cipher

    This uses letter frequency analysis to try to find the key to a ciphertext 
    encrypted with the Vigenère cipher. If 'maxkeylength' is not specified, it 
    tries to make a reasonable guess. 

    Returns: a 2-tuple (key, plaintext)
    """

    if not maxkeylength:
        maxkeylength = len(ciphertext) // 10
    key_length = 0
    max_coincidences = 0
    for shift in range(1, maxkeylength + 1):
        coincidences = sum(1 for a, b in zip(ciphertext, ciphertext[shift:]) if a == b)
        if coincidences > max_coincidences:
            key_length = shift
            max_coincidences = coincidences

    frequency_tables = []
    for start in range(key_length):
        frequency_tables.append(Counter(ciphertext[start::key_length]))

    key = []
    for table in frequency_tables:
        lettercounts = [table[letter] for letter in ALPHABET]
        distances = [dot_product(lettercounts, freq) for freq in SHIFTED_FREQUENCIES]
        key.append(distances.index(max(distances)))
    key = "".join(tochar(k) for k in key)

    return key, vigenere_decrypt(ciphertext, key)


### Tools for elementary number theory ###

def gcd(a, b):
    "Returns the GCD of a and b"

    if a == b == 0:
        raise ValueError("GCD of 0 and 0 is undefined")
    while b:
        a, b = b, a % b
    return abs(a)


def euclidean(a, b):
    "Returns g, x, y, such that g = gcd(a, b) and ax + by = g"

    if a == b == 0:
        raise ValueError("GCD of 0 and 0 is undefined")
    x1, x2 = 1, 0
    y1, y2 = 0, 1
    while True:
        q, r = divmod(a, b)
        if r == 0:
            break
        x1, x2 = x2, x1 - x2*q
        y1, y2 = y2, y1 - y2*q
        a, b = b, r
    if b < 0:
        return -b, -x2, -y2
    return b, x2, y2


def inverse(a, n):
    "Returns the inverse of a modulo n, raises ValueError if not coprime"

    d, x, y = euclidean(a, n)
    if d == 1:
        return x % n
    raise ValueError("{} is not invertible modulo {}".format(a, n))


