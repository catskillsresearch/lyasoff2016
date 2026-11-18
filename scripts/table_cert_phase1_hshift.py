import mpmath as mp, sys
mp.mp.dps=110
r=mp.mpf(5)/200
T=mp.mpf(sys.argv[1]); s=mp.mpf(sys.argv[2]); Kst=mp.mpf(sys.argv[3]); w=mp.mpf(sys.argv[4])
nu=r-s**2/2; k=Kst*T
def S4(A):
    a=1/k
    I1=(1-mp.e**(-A*a)*(1+A*a))/A**2
    I2=(2-mp.e**(-A*a)*(A**2*a**2+2*A*a+2))/A**3
    return I1-k*I2
def g4(tt,z):
    c=mp.sqrt(tt)/mp.sqrt(2*mp.pi)
    return (mp.e**(tt/2)*(c/(2j))*(mp.erf((tt+2*z)/mp.sqrt(2*tt))+mp.erf((tt-2*z)/mp.sqrt(2*tt)))
            - mp.e**(tt/8)*mp.cosh(z)*(c/1j)*(mp.erf((tt+4*z)/(2*mp.sqrt(2*tt)))+mp.erf((tt-4*z)/(2*mp.sqrt(2*tt)))))
B=2*w**(2*nu/s**2-1)*mp.e**(nu**2*T/(2*s**2))/s
def Fc(u):
    A=(2*w**2*mp.e**(nu*T)+4j*w*mp.e**(nu*T/2)*mp.sinh(u)+2)/s**2
    C=1j*8*mp.sqrt(2)*s**(-6)*w**3*mp.cosh(u)*mp.e**(nu*4*T/2-nu*T/2)/mp.sqrt(mp.pi*T)
    return B*C*g4(s**2*T,u-1j*mp.pi/2)*S4(A)
h=mp.mpf(1)/200; L=3
for th in [mp.mpf(x) for x in sys.argv[5:]]:
    vals=[Fc(n*h+1j*th) for n in range(-int(L/h),int(L/h)+1)]
    I=h*sum(vals); L1=h*sum(abs(v) for v in vals); mx=max(abs(v) for v in vals)
    print('θ',th,'∫',mp.nstr(I,12),'L1',mp.nstr(L1,4),'max',mp.nstr(mx,4),'L1/|I|',mp.nstr(L1/abs(I),4),flush=True)
