$TITLE Land Transformation
$ONTEXT
    An attempt to calibrate a quadratic model go given supply- and
    substitution (transformation) elasticities.

    Revision 2: works with just three land uses and no land use groups

    Revision 3: attempt to include groups of land uses

    Torbjörn Jansson, SLU
$OFFTEXT

SET ig Land uses and groups /forestry, pasture, arable, arable1, arable2/
    i(ig) Land uses /forestry, pasture, arable1, arable2/
    g(ig) Land classes /forestry, pasture, arable/
    g_i(g,i) Map of groups to land classes /
        forestry.forestry
        pasture.pasture
        arable.(arable1,arable2) /
    u(i,i) Upper triangular matrix of i;
ALIAS(i,j,k); ALIAS(g,h);
u(i,j) = YES $ (ORD(i) LE ORD(j));


PARAMETERS

*   --- Given data ---
    r(ig) Land rent /
    forestry    100
    pasture     200
    arable1     400
    arable2     200
    /

    y(ig) Land allocation /
    forestry    500
    pasture     100
    arable1      60
    arable2      40
    /

    elasup(ig) Elasticity of substitution /
    forestry    0.1
    pasture     0.3
    arable      0.3
    /

    elatrans(ig,ig) Elasticity of transformation (symmetric) /
    forestry.pasture    2
    forestry.arable     0.5
    pasture.arable      0.2
    arable1.arable2     1
    /

    s(g,i) Share of activity i in group g

*   --- Parameters to compute ---
    c(i)    Linear cost component
    q(i,j)  Quadratic cost component
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
    vp =E= SUM(i, vy(i)*(r(i) - c(i))) - SUM((i,j), vy(i)*q(i,j)*vy(j));

eland ..
    SUM(i, vy(i)) =L= land;

eyg(g) ..
    vy(g) =E= SUM(g_i(g,i), vy(i));

erg(g) ..
    vr(g)*vy(g) =E= SUM(g_i(g,i), r(i)*vy(i));


eH(i,j) ..
    2*vq(i,j) =E= vH(i,j)$u(i,j) + vH(j,i)$[NOT u(i,j)];

eHi(i,j) ..
    SUM(k, vHi(i,k)*[vH(k,j)$u(k,j) + vH(j,k)$(NOT u(k,j))]) =E= 1 $ SAMEAS(i,j);

eUU(i,j) $ u(i,j)..
    vH(i,j) - 0.001 $ SAMEAS(i,j)
        =E= SUM(k, vU(k,i)*vU(k,j));

eB ..
    vB =E= 1/SUM((i,j), vHi(i,j));

edydr(i,j) ..
    vdydr(i,j) =E= vHi(i,j) - SUM(k, vHi(i,k))*vB*SUM(k, vHi(k,j));

eES(i,j) ..
    vES(i,j) =E= vdydr(i,j)*r(j)/y(i);

eESg(g,h) ..
    vESg(g,h) =E= SUM((i,j)$[g_i(g,i) AND g_i(h,j)], s(g,i)*vES(i,j));

eET(i,j) ..
    vET(i,j) =E= vES(i,i) - vES(j,i);

eETg(g,h) ..
    vETg(g,h) =E= vESg(g,g) - vESg(h,g);

eFoc(i) ..
    r(i) - vc(i) - 2*SUM(j, vq(i,j)*y(j)) - lambda =E= 0;

eCrit ..
    vCrit =E= SUM(i $ elasup(i), SQR(elasup(i)-vES(i,i)))

            + SUM(g $ elasup(g), SQR(elasup(g)-vESg(g,g)))

*           + SUM((i,j) $ (elatrans(i,j) + elatrans(j,i)),
*                       SQR((elatrans(i,j) + elatrans(j,i))/2
*                           -vET(i,j)))

*           + SUM((g,h) $ (elatrans(g,h) + elatrans(h,g)),
*                       SQR((elatrans(g,h) + elatrans(h,g))/2
*                           -vETg(g,h)))
        ;

MODEL mEst Estimation model /eCrit, eFoc, eH, eHi, eUU, eB, edydr, eES, eESg, eET, eETg/;
*MODEL mSim Simulation model /ep, eland, eyg, erg/;
MODEL mSim Simulation model /ep, eland, eyg/;


*   --- Initialize levels ---
vH.L(i,i) = 100;
vHi.L(i,i) = 1/vH.L(i,i);
vU.L(i,i) = SQRT(vH.L(i,i));
vU.FX(i,j) $ [NOT u(i,j)] = 0;


SOLVE mEst USING NLP MINIMIZING vCrit;
SOLVE mEst USING NLP MINIMIZING vCrit;

q(i,j) = vq.L(i,j);
c(i) = vc.L(i);
vy.L(i) = y(i);

PARAMETER pfoc(i);
pfoc(i) = r(i) - c(i) - 2*SUM(j, q(i,j)*y(j)) - lambda ;
DISPLAY pfoc;

*   --- Check for calibration ---
SOLVE mSim USING NLP MAXIMIZING vp;
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
    d Relative shock to price/0.01/;

res("rentori",k,k) = r(k);
res("landori",k,k) = y(k);
res("elasupori",ig,ig) = elasup(ig);
res("elasupest",i,j) = vES.L(i,j);
res("elasupest",g,h) = vESg.L(g,h);
res("elatransest",i,j) = vET.L(i,j);
res("elatransori",i,j) = elatrans(i,j);
LOOP(k,
    r(k)  = r(k)*(1+d);
    res("rentsim",k,k) = r(k);
    SOLVE mSim USING NLP MAXIMIZING vp;
    r(k) = r(k)/(1+d);

    res("landsim",k,k) = vy.L(k);
    res("elasupsim",i,k) = (vy.L(i)-y(i))/y(i)/d;


    res("elatranssim",i,k) = [(vy.L(i)/vy.L(k))
                             / (y(i)/y(k)) - 1]
                            /[-d/(1+d)]
*                            /[-d]
);



EXECUTE_UNLOAD "transformation.gdx" res vq vHi vq vH vU u vET vES vESg s;
