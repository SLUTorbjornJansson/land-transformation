$TITLE Land Transformation
$ONTEXT
    An attempt to calibrate a quadratic model go given supply- and
    substitution (transformation) elasticities.

    Revision 2: works with just three land uses and no land use groups

    Revision 3: attempt to include groups of land uses

    Revision 4: added a parameter that makes costs increase steeply in lower tail

    Torbjörn Jansson, SLU
$OFFTEXT

SET ig Land uses and groups /forestry, pasture, arable, arable1, arable2, arable3/
    i(ig) Land uses /forestry, pasture, arable1, arable2, arable3/
    g(ig) Land classes /forestry, pasture, arable/
    g_i(g,i) Map of groups to land classes /
        forestry.forestry
        pasture.pasture
        arable.(arable1,arable2,arable3) /
    go(g) Only classes with several individual activities
    u(i,i) Upper triangular matrix of i;
ALIAS(i,j,k); ALIAS(g,h); ALIAS(ig,jh); ALIAS(go,ho);
u(i,j) = YES $ (ORD(i) LE ORD(j));
go(g) = YES $ [SUM(g_i(g,i), 1) gt 1];


PARAMETERS

*   --- Given data ---
    r(ig) Land rent /
    forestry    100
    pasture     200
    arable1     400
    arable2     200
    arable3     150
    /

    y(ig) Land allocation /
    forestry    500
    pasture     100
    arable1      60
    arable2      40
    arable3      10
    /

    elasup(ig) Elasticity of substitution /
    forestry    0.1
    pasture     0.3
    arable      0.3
    /

    elatrans(ig,ig) Prior elasticity of transformation (symmetric) /
*    forestry.pasture    0.1
*    forestry.arable     0.5
    pasture.arable      0.2
    arable.pasture      0.2
    arable1.arable2     1
    arable1.arable3     1
    arable2.arable1     1
    arable2.arable3     1
    arable3.arable1     1
    arable3.arable2     1
    /

    s(g,i) Share of activity i in group g

*   --- Parameters to compute ---
    c(i)    Linear cost component
    q(i,j)  Quadratic cost component
    t(i)    Tail parameter making costs increase sharply at lower tail
    land    Land endowment
    lambda  Land rent
    ;

    s(g,i) $ g_i(g,i) = y(i)/SUM(g_i(g,j), y(j));
    land = SUM(i, y(i));
    lambda = SUM(i, y(i)*r(i))/land;

*   --- Models for estimation and simulation ---

VARIABLES
*       Primal
    vy(ig)  Land allocation
    vr(g)   Group average rent
    vp      Profit

*       Dual
    vc(i)   Estimated parameter c
    vq(i,j) Estimated parameter q
    vctot   Total behavioural cost (pmp terms)
    vH(i,j) Hessian
    vHi(i,j) Hessian inverse
    vU(i,j) Upper triangular Hessian
    vB  Intermediate bracket of implicit function derivative
    vdydr(i,j) Implicit function derivative of land use i wrt rent j
    vES(ig,ig) Elasticity of supply
    vESg(ig,ig) Elasticity of supply
    vET(ig,ig) Elasticity of transformation
    vETg(ig,ig) Elasticity of transformation
    vCrit    Econometric criterion
    ;

POSITIVE VARIABLE vy;

EQUATIONS
*       Primal
    ep      Profit of operations
    ectot   Behavioural total cost (pmp terms)
    eland   Land constraint
    eyg(g)
    erg(g)

*       Dual
    eH(i,j) Hessian
    eHi(i,j) Hessian inverse
    eUU(i,j) Cholesky factorization
    eB Intermediate bracket of implicit function derivative
    edydr(i,j) Implicit function derivative of land use i wrt rent j
    eES(i,j)  Elasticity of supply for individual activities
    eESg(g,h)
    eET(i,j) Elasticity of transformation
    eETg(g,h) Elasticity of transformation
    eFoc(i) First order conditions
    eCrit   Econometric criterion
    ;

*   --- Definition of equations ---
ep ..
    vp =E= SUM(i, vy(i)*r(i)) - vctot;
*    vp =E= SUM(i, vy(i)*r(i)-c(i)) - 0.5*SUM((i,j), vy(i)*q(i,j)*vy(j));

ectot ..
    vctot =E= SUM(i, y(i)*c(i)) + 0.5*SUM((i,j), vy(i)*q(i,j)*vy(j));

eland ..
    SUM(i, vy(i)) =L= land;

eyg(g) ..
    vy(g) =E= SUM(g_i(g,i), vy(i));

erg(g) ..
    vr(g)*vy(g) =E= SUM(g_i(g,i), r(i)*vy(i));


eH(i,j) ..
    vq(i,j) =E= vH(i,j)$u(i,j) + vH(j,i)$[NOT u(i,j)];

eHi(i,j) ..
    SUM(k, vHi(i,k)*[vH(k,j)$u(k,j) + vH(j,k)$(NOT u(k,j))]) =E= 1 $ SAMEAS(i,j);

eUU(i,j) $ u(i,j)..
    vH(i,j)*(1-0.01 $ SAMEAS(i,j))
        =E= SUM(k, vU(k,i)*vU(k,j));

eB ..
    vB =E= 1/SUM((i,j), vHi(i,j));

edydr(i,j) ..
    vdydr(i,j) =E= vHi(i,j) - SUM(k, vHi(i,k))*vB*SUM(k, vHi(k,j));

eES(i,j) ..
    vES(i,j) =E= vdydr(i,j)*r(j)/y(i);

eESg(g,h) $ [go(g) OR ho(h)]..
    vES(g,h) =E= SUM((i,j)$[g_i(g,i) AND g_i(h,j)], s(g,i)*vES(i,j));

eET(i,j) $ [NOT SAMEAS(i,j)]..
    vET(i,j) =E= vES(j,j) - vES(i,j);

eETg(g,h) $ [(go(g) OR ho(h)) AND (NOT SAMEAS(g,h))]..
    vET(g,h) =E= vES(h,h) - vES(g,h);

eFoc(i) ..
    r(i) - vc(i) - SUM(j, vq(i,j)*y(j)) - lambda =E= 0;

eCrit ..
    vCrit =E= SUM(ig $ elasup(ig), SQR(elasup(ig)-vES(ig,ig)))


           + SUM((ig,jh) $ elatrans(ig,jh),
                       SQR[elatrans(ig,jh) - vET(ig,jh)])

        ;

MODEL mEst Estimation model /eCrit, eFoc, eH, eHi, eUU, eB, edydr, eES, eESg, eET, eETg, eyg, erg/;
*MODEL mSim Simulation model /ep, ectot, eland, eyg, erg/;
MODEL mSim Simulation model /ep, ectot, eland/;


*   --- Initialize levels ---
vH.L(i,i) = 100;
vHi.L(i,i) = 1/vH.L(i,i);
vU.L(i,i) = SQRT(vH.L(i,i));
vU.FX(i,j) $ [NOT u(i,j)] = 0;
vy.L(i) = y(i);

y(g)             = SUM(g_i(g,i), y(i));
vy.L(g)          = y(g);
vr.L(g) $ vy.L(g)= SUM(g_i(g,i), r(i)*vy.L(i)) / vy.L(g);
r(g) = vr.L(g);

SOLVE mEst USING NLP MINIMIZING vCrit;


q(i,j) = vq.L(i,j);
c(i) = vc.L(i);
vy.L(i) = y(i);

PARAMETER pfoc(i),pquad(i),pcmrg(i);
pfoc(i) = r(i) - c(i) - SUM(j, q(i,j)*y(j)) - lambda ;
pquad(i) = SUM(j, q(i,j)*y(j));
pcmrg(i) = c(i) + pquad(i);

DISPLAY pfoc,pquad,pcmrg, lambda;

*   --- Check for calibration ---
vy.LO(i) = y(i)*0.999;
SOLVE mSim USING NLP MAXIMIZING vp;
EXECUTE_UNLOAD "checkdata.gdx";
$stop
*   --- Run an experiment ---
SET restype /
    elasupori
    elasupsim
    rentori
    rentsim
    landori
    landsim/;

PARAMETERS
    res(*,ig,ig) Result set
    d Relative shock to price/0.001/;

res("rentori",ig,ig) = r(ig);
res("landori",ig,ig) = y(ig);
res("elasupori",ig,ig) = elasup(ig);
res("elatransori",i,j) = elatrans(i,j);

res("elasupest",ig,jh) = vES.L(ig,jh);
res("elatransest",ig,jh) = vET.L(ig,jh);
LOOP(k,
    r(k)  = r(k)*(1+d);
    res("rentsim",k,k) = r(k);
    SOLVE mSim USING NLP MAXIMIZING vp;
    r(k) = r(k)/(1+d);

    res("landsim",k,k) = vy.L(k);
    res("elasupsim",ig,k) = (vy.L(ig)-y(ig))/y(ig)/d;


    res("elatranssim",ig,k) = [(vy.L(ig)/vy.L(k))
                             / (y(ig)/y(k)) - 1]
                            /[-d/(1+d)]
);



EXECUTE_UNLOAD "transformation.gdx" res i g go vq vHi vq vH vU u vET vES vESg s;
