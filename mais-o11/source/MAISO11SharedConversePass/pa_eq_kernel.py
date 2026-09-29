"""Experimental PA-admissible equational certificate kernel, NOT an Enderton
wire-format checker and NOT a Lean certificate. Native terms are 0,S,+,variables.
D(t) and E(t) merely share the native term t+t and S(t+t). No evaluation rule
or arbitrary theorem axiom is available. Proofs may be DAGs. Induction discharges
an explicitly identified hypothesis; remaining assumptions satisfy eigenvariable
freshness. Substitution is restricted to assumption-free derivations.
"""
from dataclasses import dataclass

if not __debug__:
    raise RuntimeError("This experimental kernel requires Python assertions; do not run with -O")

@dataclass(frozen=True)
class Term:
    tag: str
    args: tuple

@dataclass(frozen=True)
class Proof:
    rule: str
    args: tuple
    lhs: int
    rhs: int
    context: tuple

class Kernel:
    def __init__(self):
        self.terms=[]; self._intern={}; self.proofs=[]
        self._subst_cache={}; self._vars_cache={}
        self._checking=False
        self.zero=self._term('0')
    def _term(self,tag,*args):
        assert type(tag) is str and tag in ('0','v','S','+')
        assert len(args)=={'0':0,'v':1,'S':1,'+':2}[tag]
        if tag=='v':assert type(args[0]) is str
        else:
            for a in args:assert type(a) is int and 0<=a<len(self.terms)
        t=Term(tag,tuple(args))
        if t not in self._intern:
            assert not self._checking, 'checking may not extend the term table'
            self._intern[t]=len(self.terms); self.terms.append(t)
        return self._intern[t]
    def var(self,name):
        assert type(name) is str
        return self._term('v',name)
    def suc(self,t): return self._term('S',t)
    def add(self,a,b): return self._term('+',a,b)
    def d(self,t): return self.add(t,t)
    def e(self,t): return self.suc(self.d(t))
    def variables(self,t):
        if t in self._vars_cache: return self._vars_cache[t]
        node=self.terms[t]
        r=frozenset([node.args[0]]) if node.tag=='v' else frozenset().union(*(self.variables(x) for x in node.args))
        self._vars_cache[t]=r; return r
    def replace(self,t,mapping):
        key=(t,tuple(sorted(mapping.items())))
        if key in self._subst_cache:return self._subst_cache[key]
        node=self.terms[t]
        if node.tag=='v':r=mapping.get(node.args[0],t)
        elif node.tag=='0':r=t
        else:r=self._term(node.tag,*(self.replace(x,mapping) for x in node.args))
        self._subst_cache[key]=r; return r
    def subst_term(self,t,mapping): return self.replace(t,mapping)
    def term_vars(self,t): return self.variables(t)
    def proof_scope(self,p): return frozenset(self.proofs[p].context)
    def is_closed(self,p): return not self.proofs[p].context
    def eq(self,p):
        p=self.proofs[p]; return p.lhs,p.rhs
    def _infer(self,rule,args,prior):
        arities={"hyp":2,"refl":1,"ax0":1,"axs":2,"sym":1,"trans":2,"cong_s":1,"cong_add":2,"subst":2,"induction":4}
        assert type(rule) is str and rule in arities
        assert type(args) is tuple and len(args)==arities[rule]
        def get(i):
            assert type(i) is int and 0<=i<prior, 'nonprior proof reference'
            return self.proofs[i]
        def term(i):
            assert type(i) is int and 0<=i<len(self.terms)
            return i
        def ctx(*ps):return tuple(sorted(set().union(*(set(p.context) for p in ps))))
        if rule=='hyp':
            a,b=map(term,args);return a,b,(prior,)
        if rule=='refl':
            a=term(args[0]);return a,a,()
        if rule=='ax0':
            a=term(args[0]);return self.add(a,self.zero),a,()
        if rule=='axs':
            a,b=map(term,args);return self.add(a,self.suc(b)),self.suc(self.add(a,b)),()
        if rule=='sym':
            p=get(args[0]);return p.rhs,p.lhs,p.context
        if rule=='trans':
            p,q=map(get,args);assert p.rhs==q.lhs,'transitivity mismatch'
            return p.lhs,q.rhs,ctx(p,q)
        if rule=='cong_s':
            p=get(args[0]);return self.suc(p.lhs),self.suc(p.rhs),p.context
        if rule=='cong_add':
            p,q=map(get,args);return self.add(p.lhs,q.lhs),self.add(p.rhs,q.rhs),ctx(p,q)
        if rule=='subst':
            p=get(args[0]);assert not p.context,'substitution of open proof prohibited'
            m=dict(args[1]);assert len(m)==len(args[1])
            for v,t in m.items():assert type(v) is str;term(t)
            return self.replace(p.lhs,m),self.replace(p.rhs,m),()
        if rule=='induction':
            v,hid,bid,sid=args;assert type(v) is str
            h,b,s=get(hid),get(bid),get(sid)
            assert h.rule=='hyp' and h.context==(hid,),'induction needs designated hypothesis'
            assert (b.lhs,b.rhs)==(self.replace(h.lhs,{v:self.zero}),self.replace(h.rhs,{v:self.zero})),'induction base mismatch'
            sv=self.suc(self.var(v))
            assert (s.lhs,s.rhs)==(self.replace(h.lhs,{v:sv}),self.replace(h.rhs,{v:sv})),'induction step mismatch'
            assert hid not in b.context,'IH occurs in induction base'
            remaining=set(ctx(b,s))-{hid}
            for aid in remaining:
                a=get(aid);assert v not in self.variables(a.lhs)|self.variables(a.rhs),'induction eigenvariable escapes'
            return h.lhs,h.rhs,tuple(sorted(remaining))
        raise AssertionError('unknown rule '+rule)
    def _proof(self,rule,*args):
        lhs,rhs,context=self._infer(rule,args,len(self.proofs))
        i=len(self.proofs);self.proofs.append(Proof(rule,tuple(args),lhs,rhs,context));return i
    def hyp(self,a,b):return self._proof('hyp',a,b)
    def refl(self,a):return self._proof('refl',a)
    def ax0(self,a):return self._proof('ax0',a)
    def axs(self,a,b):return self._proof('axs',a,b)
    def sym(self,p):return self._proof('sym',p)
    def trans(self,p,q):return self._proof('trans',p,q)
    def chain(self,*ps):
        assert ps
        p=ps[0]
        for q in ps[1:]:p=self.trans(p,q)
        return p
    def cong_s(self,p):return self._proof('cong_s',p)
    def cong_add(self,p,q):return self._proof('cong_add',p,q)
    def subst(self,p,mapping):return self._proof('subst',p,tuple(sorted(mapping.items())))
    def induction(self,var,ih,base,step):return self._proof('induction',var,ih,base,step)
    def check_all(self):
        # The serialized table is immutable during checking: inference may only
        # recover already declared nodes. Otherwise a malformed axiom could add
        # a bad node after the term-table validation pass.
        self._subst_cache={};self._vars_cache={}
        assert type(self.zero) is int and 0<=self.zero<len(self.terms),'invalid zero reference'
        for i,t in enumerate(self.terms):
            assert type(t) is Term and type(t.tag) is str and type(t.args) is tuple
            assert t.tag in ('0','v','S','+')
            assert len(t.args)=={'0':0,'v':1,'S':1,'+':2}[t.tag]
            if t.tag=='v':assert type(t.args[0]) is str
            else:
                for a in t.args:assert type(a) is int and 0<=a<i
        assert len(set(self.terms))==len(self.terms),'terms must be hashconsed'
        self._intern={t:i for i,t in enumerate(self.terms)}
        assert self.terms[self.zero]==Term('0',())
        for i,p in enumerate(self.proofs):
            assert type(p) is Proof
            for t in (p.lhs,p.rhs):assert type(t) is int and 0<=t<len(self.terms),'invalid proof endpoint'
            assert type(p.context) is tuple
            for a in p.context:assert type(a) is int and 0<=a<=i
            assert tuple(sorted(set(p.context)))==p.context
        old_size=len(self.terms)
        self._checking=True
        try:
            for i,p in enumerate(self.proofs):
                result=self._infer(p.rule,p.args,i)
                assert result==(p.lhs,p.rhs,p.context),('incorrect proof node',i)
            assert len(self.terms)==old_size
        finally:
            self._checking=False
        return True
    def check_closed(self,p):
        assert type(p) is int and 0<=p<len(self.proofs),'invalid final proof reference'
        self.check_all();assert not self.proofs[p].context,'undischarged assumptions';return True

def build_lemmas(k):
    """Fixed proofs of additive monoid laws from the two PA addition axioms.
    Variable names in returned templates: zero_left(x), suc_left(x,y),
    assoc(a,b,c), comm(a,b), shuffle(a,b,c,d).
    """
    z=k.zero;x=k.var('x');y=k.var('y')
    ih=k.hyp(k.add(z,x),x)
    zl=k.induction('x',ih,k.ax0(z),k.trans(k.axs(z,x),k.cong_s(ih)))
    ih=k.hyp(k.add(k.suc(x),y),k.suc(k.add(x,y)))
    base=k.trans(k.ax0(k.suc(x)),k.sym(k.cong_s(k.ax0(x))))
    step=k.chain(k.axs(k.suc(x),y),k.cong_s(ih),k.sym(k.cong_s(k.axs(x,y))))
    sl=k.induction('y',ih,base,step)
    a,b,c,d=[k.var(v) for v in 'abcd']
    ih=k.hyp(k.add(k.add(a,b),c),k.add(a,k.add(b,c)))
    base=k.trans(k.ax0(k.add(a,b)),k.sym(k.cong_add(k.refl(a),k.ax0(b))))
    step=k.chain(k.axs(k.add(a,b),c),k.cong_s(ih),k.sym(k.axs(a,k.add(b,c))),k.cong_add(k.refl(a),k.sym(k.axs(b,c))))
    assoc=k.induction('c',ih,base,step)
    ih=k.hyp(k.add(a,b),k.add(b,a))
    base=k.trans(k.ax0(a),k.sym(k.subst(zl,{'x':a})))
    step=k.chain(k.axs(a,b),k.cong_s(ih),k.sym(k.subst(sl,{'x':b,'y':a})))
    comm=k.induction('b',ih,base,step)
    def A(a,b,c):return k.subst(assoc,{'a':a,'b':b,'c':c})
    # (a+b)+(c+d) = a+(b+(c+d)) = a+((b+c)+d)
    # = a+((c+b)+d) = a+(c+(b+d)) = (a+c)+(b+d).
    shuffle=k.chain(A(a,b,k.add(c,d)),
        k.cong_add(k.refl(a),k.sym(A(b,c,d))),
        k.cong_add(k.refl(a),k.cong_add(k.subst(comm,{'a':b,'b':c}),k.refl(d))),
        k.cong_add(k.refl(a),A(c,b,d)),k.sym(A(a,c,k.add(b,d))))
    out=dict(zero_left=zl,suc_left=sl,assoc=assoc,comm=comm,shuffle=shuffle)
    k.check_all()
    assert all(not k.proofs[p].context for p in out.values())
    return out

class BinaryArithmetic:
    """Explicit addition proofs for shared canonical D/E binary numerals.

    num(0)=0, num(2h)=D(num(h)) for h>0, num(2h+1)=E(num(h)).
    Arithmetic on Python ints chooses the proof to print, but the kernel never
    uses those integers to accept an equation. add_proof and succ_proof cache
    proof DAGs. Each recursion decreases bit length. Addition uses O(B^2)
    primitive inference nodes for B-bit inputs (a conservative bound); successor
    uses O(B). These counts are not yet Enderton serialized-character bounds.
    """
    def __init__(self,k,lemmas=None):
        self.k=k; self.lemmas=lemmas if lemmas is not None else build_lemmas(k)
        self._nums={0:k.zero};self._adds={};self._succs={}
    def num(self,n):
        assert isinstance(n,int) and n>=0
        if n not in self._nums:
            t=self.num(n//2)
            self._nums[n]=self.k.e(t) if n%2 else self.k.d(t)
        return self._nums[n]
    def succ_proof(self,n):
        assert isinstance(n,int) and n>=0
        if n in self._succs:return self._succs[n]
        k=self.k
        if n==0:p=k.sym(k.cong_s(k.ax0(k.zero)))
        elif n%2==0:p=k.refl(k.suc(self.num(n)))
        else:
            h=self.num(n//2)
            # D(S(h)) = S(h+S(h)) = S(S(h+h)).
            q=k.trans(k.subst(self.lemmas['suc_left'],{'x':h,'y':k.suc(h)}),k.cong_s(k.axs(h,h)))
            ih=self.succ_proof(n//2)
            p=k.trans(k.sym(q),k.cong_add(ih,ih))
        assert k.eq(p)==(k.suc(self.num(n)),self.num(n+1))
        self._succs[n]=p;return p
    def add_proof(self,a,b):
        assert isinstance(a,int) and isinstance(b,int) and min(a,b)>=0
        key=a,b
        if key in self._adds:return self._adds[key]
        k=self.k
        if a==0:p=k.subst(self.lemmas['zero_left'],{'x':self.num(b)})
        elif b==0:p=k.ax0(self.num(a))
        else:
            h,j=self.num(a//2),self.num(b//2)
            inner=self.add_proof(a//2,b//2)
            q=k.trans(k.subst(self.lemmas['shuffle'],{'a':h,'b':h,'c':j,'d':j}),k.cong_add(inner,inner))
            if a%2==0 and b%2==0:p=q
            elif a%2==0:p=k.trans(k.axs(k.d(h),k.d(j)),k.cong_s(q))
            elif b%2==0:p=k.trans(k.subst(self.lemmas['suc_left'],{'x':k.d(h),'y':k.d(j)}),k.cong_s(q))
            else:
                p=k.chain(k.subst(self.lemmas['suc_left'],{'x':k.d(h),'y':k.e(j)}),
                    k.cong_s(k.axs(k.d(h),k.d(j))),k.cong_s(k.cong_s(q)),
                    self.succ_proof(2*(a//2+b//2)+1))
        assert k.eq(p)==(k.add(self.num(a),self.num(b)),self.num(a+b))
        self._adds[key]=p;return p

if __name__=='__main__':
    k=Kernel();ls=build_lemmas(k)
    print('Fixed PA-admissible templates checked:', ', '.join(ls))
    print('Native term DAG nodes:',len(k.terms),'proof DAG nodes:',len(k.proofs))
    # This test is a validator smoke test, not a proof of validator correctness.
    from dataclasses import replace
    target=ls['shuffle'];old=k.proofs[target]
    k.proofs[target]=replace(old,rhs=k.zero)
    try:k.check_all()
    except AssertionError:print('Tampered endpoint rejected')
    else:raise AssertionError('tampering accepted')
    k.proofs[target]=old
    try:k.check_closed(k.hyp(k.zero,k.suc(k.zero)))
    except AssertionError:print('Undischarged false hypothesis rejected')
    else:raise AssertionError('open proof accepted')

    # Rule-scope attacks: open substitution, circular references and invalid
    # induction instances must be rejected by the same checker used above.
    def rejects(action,label):
        try: action()
        except (AssertionError,IndexError,ValueError,TypeError): print(label,'rejected')
        else: raise AssertionError(label+' accepted')
    open_eq=k.hyp(k.var('u'),k.zero)
    rejects(lambda:k.subst(open_eq,{'u':k.suc(k.zero)}),'Open substitution')
    rejects(lambda:k._proof('sym',len(k.proofs)),'Forward proof reference')
    h=k.hyp(k.var('n'),k.zero)
    rejects(lambda:k.induction('n',h,k.refl(k.zero),h),'Incorrect induction step')
    # Valid-looking induction carrying a forbidden open eigenvariable premise.
    n=k.var('n'); external=k.hyp(k.suc(n),k.zero)
    rejects(lambda:k.induction('n',h,k.refl(k.zero),external),'Escaping induction eigenvariable')
    kk=Kernel();ba=BinaryArithmetic(kk)
    for a in range(32):
        for b in range(32):ba.add_proof(a,b)
    for a in range(100):ba.succ_proof(a)
    kk.check_all()
    print('1024 addition cases and 100 successor cases checked')
    kk=Kernel();ba=BinaryArithmetic(kk)
    cert=ba.add_proof(2**256-1,2**256-1)
    kk.check_closed(cert)
    print('256-bit carry proof checked:',len(kk.proofs),'proof nodes;',len(kk.terms),'term nodes')

    def bad_zero():
        bad=Kernel();bad.zero=-1
        bad.proofs.append(Proof('ax0',(0,),1,0,()))
        bad.check_all()
    rejects(bad_zero,'Negative zero reference exploit')
    def undeclared_result():
        bad=Kernel();bad.proofs.append(Proof('ax0',(0,),0,0,()))
        before=len(bad.terms)
        try:bad.check_all()
        finally:assert len(bad.terms)==before,'checker mutated term table'
    rejects(undeclared_result,'Undeclared expected axiom term')
    def bool_endpoint():
        bad=Kernel();bad.proofs.append(Proof('refl',(0,),False,0,()))
        bad.check_all()
    rejects(bool_endpoint,'Boolean proof endpoint')
