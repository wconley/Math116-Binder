#!/usr/bin/env python3
# coding: utf-8

from itertools import cycle
from collections import Counter
import functools
import operator
import re


### Tools for very basic encodings/decodings ###

ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

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

def text_to_num(message):
    "Encodes text to a large number, two digits per letter"
    m = 0
    for char in cleanstring(message):
        m = 100*m + tonum(char) + 1
    return m

def num_to_text(number):
    "Decodes a number into text, two digits per letter"
    plaintext = []
    while number:
        number, letter = divmod(number, 100)
        plaintext.append(tochar(letter - 1))
    return "".join(reversed(plaintext))


### Tools for primitive ciphers (Caesar, Vigenère, etc) ###

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
    raise ValueError(f"{a} is not invertible modulo {n}")


def crt(residues, moduli):
    """Performs the Chinese Remainder Theorem

    Returns a pair (x, n) where n is the product of the moduli in the second 
    argument, and x is congruent to each residue in the first argument modulo 
    the corresponding modulus from the second argument. 

    Note that if you have the residues and moduli already paired off, you can 
    just "un-pair" them with zip, e.g.: 
        crt(*zip((2, 5), (4, 7), (1, 11))) # returns (67, 385)

    This will raise ValueError if the moduli are not pairwise relatively prime. 
    """

    bigresidue = 0
    bigmodulus = functools.reduce(operator.mul, moduli, 1)
    for a, m in zip(residues, moduli):
        y = bigmodulus // m
        z = inverse(y, m) # This will raise ValueError if y is not coprime to m
        bigresidue = (bigresidue + a*y*z) % bigmodulus
    return bigresidue, bigmodulus


def crt_basic(a1, a2, m1, m2):
    """Performs the Chinese Remainder Theorem on a system of TWO congruences

    This function ONLY WORKS with a system of two congruences, and only works 
    if the two moduli m1 and m2 are coprime. In that case, the modulus of the 
    result should just be m1 * m2, so this function doesn't bother returning 
    that modulus. It just computes and returns a residue x that is congruent to 
    a1 modulo m1 and is congruent to a2 modulo m2. 

    This will raise ValueError if the moduli m1 and m2 are not relatively prime. 
    """

    g, i1, i2 = euclidean(m1, m2)
    if g == 1:
        return (a1 * m2 * i2 + a2 * m1 * i1) % (m1 * m2)
    raise ValueError(f"{m1} and {m2} are not coprime")


def crt_general(residues, moduli):
    """Performs the Chinese Remainder Theorem

    Returns a pair (x, n) where n is the least common multiple of the moduli in 
    the second argument, and x is congruent to each residue in the first 
    argument modulo the corresponding modulus from the second argument. 

    Note that if you have the residues and moduli already paired off, you can 
    just "un-pair" them with zip, e.g.: 
        crt_general(*zip((2, 5), (4, 7), (1, 11))) # returns (67, 385)

    This version works even if the moduli are not pairwise relatively prime, if 
    there is a solution. It will raise ValueError if there is no solution. 
    """

    a1 = 0
    m1 = 1
    for a2, m2 in zip(residues, moduli):
        g, i1, i2 = euclidean(m1, m2)
        q1, r1 = divmod(a1, g)
        q2, r2 = divmod(a2, g)
        if r1 != r2:
            raise ValueError("No solution to this system of congruences")
        new_m = m1 * m2 // g
        a1 = (q1 * m2 * i2 + q2 * m1 * i1 + r1) % new_m
        m1 = new_m
    return a1, m1


def pseudoprime(n, base):
    """Perform the Miller–Rabin (strong pseudoprime) test on n

    Note that in some (rare) cases, the Miller–Rabin test can actually produce 
    a non-trivial factorization of n, however this function does not return 
    those factors. If you want to run this same algorithm, but obtain that 
    factorization when possible, you can use the 'universal_exponent_factor' 
    function in this library, and pass it n and n - 1. But note that it is 
    likely to raise ValueError if n is not prime. See its documentation. 

    Returns True or False
    If this returns True, n is either prime or a strong pseudoprime for 'base'. 
    If this returns False, n is guaranteed to be composite. 
    """

    if n == 2:
        return True
    if n % 2 == 0:
        return False
    exp = 1
    oddpart = (n - 1) // 2
    while oddpart % 2 == 0:
        exp += 1
        oddpart //= 2
    x = pow(base, oddpart, n)
    if x == 1 or x == n - 1:
        return True
    for i in range(1, exp):
        newx = x*x % n
        if newx == n - 1:
            return True
        if newx == 1:
            return False
        x = newx
    return False


def is_probably_prime(n, bases=(2, 3, 5, 7, 11)):
    "Check if n is prime, by running Miller–Rabin test for several bases"
    return all(pseudoprime(n, base) for base in bases)


### Factoring algorithms ###

def factor(n):
    "Returns the factorization of n by trial division, using the PRIMES list"

    if n == 0:
        raise ValueError("Cannot factor 0")
    factors = Counter()
    if n < 0:
        n = -n
        factors[-1] = 1
    for p in PRIMES:
        while n % p == 0:
            factors[p] += 1
            n //= p
        if n == 1:
            break
    else:
        raise ValueError("n has a 'large' prime factor. Known factorization "
                         f"{factors}. Remaining unfactored part {n}")
    return factors


def universal_exponent_factor(n, exponent, bases=(2, 3, 5, 7, 11)):
    """Factor 'n', given that 'exponent' is a universal exponent for n

    A universal exponent is a positive integer e for which 
        b^e = 1 (mod n)
    for any b that is relatively prime to n. If n is prime, then e is a 
    universal exponent for n iff e is a multiple of n - 1 (Fermat's Little 
    Theorem for one direction, existence of primitive roots for the other). 
    More generally, for any n, \phi(n) is a universal exponent for n (Euler's 
    Theorem). 

    This algorithm is not guaranteed to produce a factorization of n, but it's 
    very likely to. If it cannot find one, it will return None. In particular, 
    providing this function with a number n, and n - 1 as the (supposed) 
    universal exponent will do the equivalent of the Miller–Rabin (strong 
    pseudoprime) test on n for the bases in 'bases'. In that case, if the 
    function returns None, then the number is very very likely to be prime. 
    (Note that when used this way, this function will most likely raise 
    ValueError if n is not prime.) 

    Returns a nontrivial factor of n, or None if it can't find one
    Raises ValueError if it is found that 'exponent' is not universal
    """

    oddpart = exponent
    exp = 0
    while oddpart % 2 == 0:
        oddpart //= 2
        exp += 1
    for b in bases:
        if n == b:
            return None
        if n % b == 0:
            return b
        x = pow(b, oddpart, n)
        for i in range(exp):
            if x == 1 or x == n - 1:
                break
            newx = x*x % n
            if newx == 1:
                return gcd(x - 1, n)
            x = newx
        else:
            raise ValueError(f"{exponent} is not a universal exponent for {n}")


def pollard_factor(n, bases=(2,), bound=100000):
    "Runs the Pollard p - 1 factoring algorithm on n"

    for b in bases:
        power = b
        for k in range(2, bound):
            power = pow(power, k, n)
            if k % 200 == 0: # Every 200th step, check status
                if power == 1:
                    break # We could try the exponent factoring algorithm here, 
                          # but that would require computing factorial(k)
                factor = gcd(power - 1, n)
                if factor == n:
                    break
                if factor != 1:
                    return factor
    return None


# A list of all primes less than 10,000
PRIMES = [
    2, 3, 5, 7, 
    11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 
    89, 97, 
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 
    179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 
    263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 
    353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 
    443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 
    547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 
    641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 
    739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 
    839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 
    947, 953, 967, 971, 977, 983, 991, 997, 
    1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 
    1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 
    1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 
    1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 
    1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 
    1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 
    1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 
    1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 
    1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 
    1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 
    1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 
    1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 
    2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 
    2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 
    2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 
    2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 
    2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 
    2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 
    2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 
    2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 
    2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 
    2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 
    3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 
    3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 
    3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 
    3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 
    3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 
    3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 
    3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 
    3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 
    3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 
    3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 
    4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 
    4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 
    4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 
    4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 
    4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 
    4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 
    4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 
    4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 
    4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 
    4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 
    5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 
    5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 
    5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 
    5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 
    5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 
    5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 
    5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 
    5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 
    5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 
    5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 
    6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 
    6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 
    6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 
    6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 
    6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 
    6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 
    6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 
    6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 
    6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 
    7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 
    7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 
    7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 
    7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 
    7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 
    7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 
    7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 
    7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 
    7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 
    8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 
    8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 
    8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 
    8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 
    8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 
    8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 
    8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 
    8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 
    8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 
    8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 
    9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 
    9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 
    9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 
    9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 
    9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 
    9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 
    9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 
    9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 
    9931, 9941, 9949, 9967, 9973, 
]


