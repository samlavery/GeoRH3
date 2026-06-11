import mpmath as mp
mp.mp.dps = 40
def L(s):
    return mp.power(3,-s)*(mp.zeta(s, mp.mpf(1)/3) - mp.zeta(s, mp.mpf(2)/3))
print('L(1/2, chi3) =', mp.nstr(L(mp.mpf('0.5')), 25))
print('1/6 * L(1/2) =', mp.nstr(L(mp.mpf('0.5'))/6, 25))
print('|L(1/2+8.0397i)| =', mp.nstr(abs(L(mp.mpf('0.5')+1j*mp.mpf('8.0397371556814666817136232141729658027930102674'))),5))
