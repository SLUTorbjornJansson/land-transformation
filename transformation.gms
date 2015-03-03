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
    ;

    s(g,i) $ g_i(g,i) = y(i)/SUM(g_i(g,j), y(j));

*   --- Models for estimation and simulation ---

VARIABLES
*       Primal
    vy(i)   Land allocation
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
    vCrit    Econometric criterion
    ;

EQUATIONS
*       Primal
    ep      Profit of operations
    eland   Land constraint

*       Dual
    eH(i,j) Hessian
    eHi(i,j) Hessian inverse
    eUU(i,j) Cholesky factorization
    eB Intermediate bracket of implicit function derivative
    edydr(i,j) Implicit function derivative of land use i wrt rent j
    eES(i,j)  Elasticity of supply for individual activities
    eESg(g,h)
    eET(i,j) Elasticity of transformation
    eFoc(i) First order conditions
    eCrit   Econometric criterion
    ;

*   --- Definition of equations ---
ep ..
    vp =E= SUM(i, vy(i)*(r(i) - c(i))) - SUM((i,j), vy(i)*q(i,j)*vy(j));

eland ..
    SUM(i, vy(i)) =L= land;

eH(i,j) ..
    vH(i,j) =E= 2*vq(i,j);

eHi(i,j) ..
    SUM(k, vHi(i,k)*vH(k,j)) =E= 1 $ SAMEAS(i,j);

eUU(i,j) ..
    vH(i,j) - 0.0001 $ SAMEAS(i,j)
        =E= SUM(k $ (u(i,k) AND u(j,k)), vU(k,i)*vU(k,j));

eB ..
    vB =E= 1/SUM((i,j), vHi(i,j));

edydr(i,j) ..
    vdydr(i,j) =E= vHi(i,j) - SUM(k, vHi(i,k))*vB*SUM(k, vHi(k,j));

eES(i,j) ..
    vES(i,j) =E= vdydr(i,j)*r(j)/y(i);

eESg(g,h) ..
    vESg(g,h) =E= SUM((i,j)$[g_i(g,i) AND g_i(h,j)], s(g,i)*vES(i,j));

eET(i,j) ..
    -vET(i,j) =E= vES(j,i) - vES(i,i);

eFoc(i) ..
    r(i) - vc(i) - 2*SUM(j, vq(i,j)*y(j)) =E= 0;

eCrit ..
    vCrit =E= SUM(i $ elasup(i), SQR(elasup(i)-vES(i,i)))
            + SUM((i,j) $ (elatrans(i,j) + elatrans(j,i)),
                        SQR((elatrans(i,j) + elatrans(j,i))/2
                            -vET(i,j)))
        ;

MODEL mEst Estimation model /eCrit, eFoc, eH, eHi, eUU, eB, edydr, eES, eESg, eET/;
MODEL mSim Simulation model /ep, eland/;


*   --- Initialize levels ---
vH.L(i,i) = 100;
vHi.L(i,i) = 1/vH.L(i,i);
vU.L(i,i) = SQRT(vH.L(i,i));


SOLVE mEst USING NLP MINIMIZING vCrit;

q(i,j) = vq.L(i,j);
c(i) = vc.L(i);
land = SUM(i, y(i));

*   --- Check for calibration ---
SOLVE mSim USING NLP MAXIMIZING vp;

*   --- Run an experiment ---
SET restype /
    elasupori
    elasupsim
    rentori
    rentsim
    landori
    landsim/;

PARAMETERS
    res(*,i,j) Result set
    d Relative shock to price/0.01/;

res("rentori",k,k) = r(k);
res("landori",k,k) = y(k);
res("elasupori",k,k) = elasup(k);
res("elasupest",i,j) = vES.L(i,j);
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



EXECUTE_UNLOAD "transformation.gdx" res vq vHi vq vH vET vES vESg s;
