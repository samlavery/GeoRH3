import numpy as np
def chi3(n): return [0,1,-1][n%3]
N=400; U=400.0; M=32768
u=np.linspace(0,U,M,endpoint=False); du=u[1]-u[0]
n=np.arange(1,N+1); amp=np.array([chi3(k) for k in range(1,N+1)])/np.sqrt(n); logn=np.log(n)
L=(amp[None,:]*np.exp(-1j*np.outer(u,logn))).sum(1)
F=np.abs(np.fft.fft(L)); freq=2*np.pi*np.fft.fftfreq(M,d=du)
# top positive-frequency peaks (exclude DC = n=1)
mask=(freq>0.4)&(freq<3.0); fr=freq[mask]; fm=F[mask]
order=np.argsort(fm)[::-1]
peaks=[]
for i in order:
    f=fr[i]
    if all(abs(f-p)>0.05 for p in peaks): peaks.append(round(f,3))
    if len(peaks)>=10: break
print("shift-flow spectrum (FFT peaks of L(u)) :", sorted(peaks))
print("log n  (n=2..11)                        :", [round(np.log(k),3) for k in range(2,12)])
print("the zeros gamma_n                       :", [8.04,11.25,15.70,18.26,20.46])
# dips of |L(u)| are the zeros (the cancellation events), NOT the spectrum
ag=np.abs(L); dips=[u[i] for i in range(1,len(ag)-1) if ag[i]<ag[i-1] and ag[i]<ag[i+1] and ag[i]<0.25]
print("\ndips of |L(u)| (cancellation events)    :", [round(d,2) for d in dips[:6]])
print("=> shift-flow EIGENVALUES = {log n} (integers); the ZEROS are the DIPS, not the spectrum.")
