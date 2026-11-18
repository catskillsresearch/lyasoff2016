import mpmath as mp, sys
mp.mp.dps=int(sys.argv[1]) if len(sys.argv)>1 else 150
r=mp.mpf(5)/200
def setup(T,s,K):
    return dict(T=mp.mpf(T),s=mp.mpf(s),nu=r-mp.mpf(s)**2/2,k=mp.mpf(K)*mp.mpf(T))
def S4(k,A):
    a=1/k
    # ∫_0^a (v - k v^2) e^{-Av} dv
    I1=(1-mp.e**(-A*a)*(1+A*a))/A**2
    I2=(2-mp.e**(-A*a)*(A**2*a**2+2*A*a+2))/A**3
    return I1-k*I2
def g4(tt,z):
    st=mp.sqrt(tt); c=st/mp.sqrt(2*mp.pi)
    return (mp.e**(tt/2)*(c/(2j))*(mp.erf((tt+2*z)/mp.sqrt(2*tt))+mp.erf((tt-2*z)/mp.sqrt(2*tt)))
            - mp.e**(tt/8)*mp.cosh(z)*(c/1j)*(mp.erf((tt+4*z)/(2*mp.sqrt(2*tt)))+mp.erf((tt-4*z)/(2*mp.sqrt(2*tt)))))
def F(P,u,w):
    s,nu,t,k=P['s'],P['nu'],P['T'],P['k']
    A=(2*w**2*mp.e**(nu*t)+4j*w*mp.e**(nu*t/2)*mp.sinh(u)+2)/s**2
    B=2*w**(2*nu/s**2-1)*mp.e**(nu**2*t/(2*s**2))/s
    C=1j*8*mp.sqrt(2)*s**(-6)*w**3*mp.cosh(u)*mp.e**(nu*4*t/2-nu*t/2)/mp.sqrt(mp.pi*t)
    return (B*C*g4(s**2*t,u-1j*mp.pi/2)*S4(k,A)).real
P=setup('0.5','0.22','1.0')
for w in ['0.5','0.9','1.0','1.1','1.5','3']:
    row=[]
    for u in ['0','0.5','1','2','4','8']:
        row.append(mp.nstr(F(P,mp.mpf(u),mp.mpf(w)),3))
    print(w,row)
