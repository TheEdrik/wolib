# Routing example: SAT/CNF representation

Visegrady, Tamas ```<tamas@visegrady.ch>```

# Introduction

We describe the SAT-solver representation of routing problems used by
our pack-and-route algorithm.

# Time and delivery representation

Our data representation is somewhat redundant, simplifying SAT problem
formulation. We organize variables around (delivery, time unit, vehicle)
tuples, with the 'unit' quantization mapping minute-based time into
manageable units (currently, 15 minutes).

While arrival and departure times are tracked in minutes, the coarser
units serve as initial filters, and conveniently, as a unit of
allocation. We currently assume that *no more than one delivery may be
mapped to a single unit.* The restriction might be relaxed later, but
some of our approximations---particularly, about timing slack around
deliveries---essentially prohibit completing more than one delivery per
unit per vehicle. (See separate description of how merged deliveries
would be still scheduled to complete within a single unit, if they are
in close physical proximity.)

With the unit-based quantization of time, assuming not more than
```2^N-1``` vehicles, the basic representation would be a cross-bar of
deliveries (an integer ID), time units (an index), and the number of
vehicle assigned to delivering in that time unit. The vehicle ID is
encoded into ```N``` bits, with an all-```0``` combination indicating
'unassigned'. (In other words, for SAT-solver representation purposes,
our vehicle-number assignments are ```1```-based.)

The entire encoding assigns a collection of variables cross-referencing
the delivery/time/vehicle tuple:

```dXX tYY v0 .. v(N-1)```

Here, ```dXX tYY``` specifies the delivery ```XX``` and time unit
```YY```, with the ```v``` bits showing the vehicle assignment. In other
words, arrival of vehicle number ```2``` it time window ```3``` to
deliver delivery ```6``` will set the following variables with ```N=4```
(```v=0010```):

```
d06 - t03 - v0=False
d06 - t03 - v1=False
d06 - t03 - v2=True
d06 - t03 - v3=False
```

We also construct a logical OR of all ```dXXtYYv...``` variables for
the same ```XX``` and ```YY```. With our 1-based encoding of vehicle
numbers, this OR indicates that the delivery is scheduled in that time
unit, by the indicated vehicle; in the above example, ```d06 t03```
would be True.

# Representation of restrictions

Restrictions intersect the following requirements (shown here through
their SAT/CNF variables):

1. Every delivery is scheduled in exactly one time unit. With the above
logical OR, exactly one of ```dXX tYY``` variables must be true
for each delivery ```XX```.

    The SAT/CNF representation is a set of exactly-one clauses
    for each delivery index ```dXX```.

2. Delivery + time windows which would be spatially problematic are
prohibited. One may construct this example over pairwise combinations
by cross-checking any possible combination of ```dXX tYY``` and ```dWW
tZZ``` pairs. Spatial---and inferred minimal temporal---distance between
delivery points of ```XX``` and ```WW``` limit whether the same vehicle
would be able to service them in units ```YY``` and ```ZZ```.

    For colliding ```dXX tYY``` and ```dWW tZZ``` pairs, which may
    not be serviced by the same vehicle, the condition ensures
    that:

    2.1. Either one of the vehicle-assigned (```vN```) auxiliary
    variables is all-```0``` (indicating no vehicle assignment) or

    2.2. The two ```N```-bit vehicle indexes assigned to
    ```dXX tYY``` and ```dWW tZZ``` differ. (In other words, potentially
    colliding delivery+time unit combinations MUST be assiged to
    different vehicles, which the ```vN``` bits encode.)

3. As a direct consequence of prohibiting any conflicting pair of
delivery+time combinations, we ensure that each vehicle is presented by
a valid schedule. (While our conflict prevention only protects against
pairwise conflicts, aggregating non-conflicting pairs into a global
schedule preserves schedule feasibility.)

# Fully expanded trivial example

A small delivery of two deliveries (d1, d2), not more than two vehicles
and therefore two vehicle bits (v1, v2), and a total of five available
time units (t0..t4) are considered. The following list of variables and
their Boolean expressions are considered:

```
d1t0'v0 d1t0'v1    ---------------     d1 may be delivered 0800-0859, inclusive
d1t1'v0 d1t1'v1    d2t1'v0 d2t1'v1     d2 may be delivered 0815-0914, inclusive
d1t2'v0 d1t2'v1    d2t2'v0 d2t2'v1
d1t3'v0 d1t3'v1    d2t3'v0 d2t3'v1
---------------    d2t4'v0 d2t4'v1
```

Note that the apostrophe separators are added here for readability; the
SAT/CNF generator in the pack-and-route core generates all-alphanumeric
identifiers.

We also assume that ```d1``` and ```d2``` coordinates imply that the
deliveries may not be performed in the same, or even adjacent time
units. (In other words, including delivery overhead, the two deliveries
MUST be assigned at least two units apart.)

Since (```v0, v1```) encode unassigned by ```00```---and we ignore 11
for this example---the following auxiliary conditions hold:

1. if (```dXXtYY'v0, dXXtYY'v1```) is not ```00```, the vehicle with ID
```v0v1``` is assigned to this delivery in time unit ```YY```.

2. the derived ```dXXtYY``` compound variables---logical ```OR``` of its
vehicle-extended bits ```dXXtYY'v0...``` marks that the delivery has been
scheduled to time unit ```YY```.

3. if each delivery MUST be scheduled, exactly one of the ```dXXtYY```
variables for delivery ```XX``` MUST be True.

4. if the delivery MAY be delayed, the above condition turns into *not
more than one ```dXXtYY``` variable* instead of *exactly one*.

5. auxiliary variables, which mirror per-delivery+time ```v0``` and
```v1``` bits, summarize which vehicle has been assigned to the
delivery. These ```dXXv0``` and ```dXXv1``` bits are simply the logical
```OR``` of the corresponding ```v0``` and ```v1``` over all applicable
time units (in the ```d1``` case, ```t0...t3```).

    These auxiliary variables are simply an ```OR```, since an
    unassigned combination is represented as the all-00 combination.
    Therefore, only one of the combinations may not be all-```00```, and
    ```OR```ing the "columns" trivially creates the summary variables.
    (The latter is useful to detect deliveries assigned to the same
    vehicle; see below.)

6. The conditions of not less than two time units' difference between
```d1``` and ```d2``` prohibit the following pairs of delivery+time unit
assignments from using the same vehicle:

```
d1t1  and  d2t1         --- delivery possibilities in the same time unit
d1t2  and  d2t2
d1t3  and  d2t3

d1t0  and  d2t1         --- possibilities with only one time unit difference
d1t1  and  d2t2         --- d2 follows d1
d1t2  and  d2t3
d1t3  and  d2t4

d1t2  and  d2t1         --- d1 follows d2
d1t3  and  d2t2
```

    The "assigned to different vehicles" condition is straightforward to
    represent: the ```v0v1``` bit combination of the two ```dXXtYY```
    pairs MUST be different, or either one may be 00 (since this means
    unassigned).

    The above list of conflicting delivery+time unit pairs therefore
    expands to "either one is ```00```, or the two combinations differ"
    conditions for the following two-bit ```v0+v1``` values:

```
(d1t1'v0, d1t1'v1)  and  (d2t1'v0, d1t1'v1)
(d1t2'v0, d1t1'v1)  and  (d2t2'v0, d1t1'v1)
(d1t3'v0, d1t1'v1)  and  (d2t3'v0, d1t1'v1)

(d1t0'v0, d1t1'v1)  and  (d2t1'v0, d1t1'v1)
(d1t1'v0, d1t1'v1)  and  (d2t2'v0, d1t1'v1)
(d1t2'v0, d1t1'v1)  and  (d2t3'v0, d1t1'v1)
(d1t3'v0, d1t1'v1)  and  (d2t4'v0, d1t1'v1)

(d1t2'v0, d1t1'v1)  and  (d2t1'v0, d1t1'v1)
(d1t3'v0, d1t1'v1)  and  (d2t2'v0, d1t1'v1)
```

As an example, if ```d1t3'v0v1``` and ```d2t3'v0v1``` (1) are both
non-```00``` and (2) their two-bit ```v0+v1``` combinations are
identical, the schedule is invalid: they are assigned to the same
vehicle.

# Example logs

The following conflicts have been registered between ```D1``` and
```D56``` (*minimal delivery separation 75 minutes*) and ```D1``` and
```D57``` (minimal separation 45 minutes), respectively:

```
CONFLICT DELV1=1,T=1300-1314 DELV2=56,T=1400-1414 MIN.TIME.DIFF=75min
COMPAT[1,56]: TIME.VEC=[1215-1315]=x1e0000,[1400-1500+1015-1115]=xf001e00, ...
    MIN.TIME.DIFF=75min, CONFLICTS=1

CONFLICT DELV1=1,T=1215-1229 DELV2=57,T=1145-1159 MIN.TIME.DIFF=45min
CONFLICT DELV1=1,T=1215-1229 DELV2=57,T=1200-1214 MIN.TIME.DIFF=45min
CONFLICT DELV1=1,T=1230-1244 DELV2=57,T=1200-1214 MIN.TIME.DIFF=45min
CONFLICT DELV1=1,T=1300-1314 DELV2=57,T=1330-1344 MIN.TIME.DIFF=45min
COMPAT[1,57]: TIME.VEC=[1215-1315]=x1e0000,[1115-1215+1330-1530]=x3fc1e000, ...
    MIN.TIME.DIFF=45min, CONFLICTS=4
```

The above reported conflicting assignments in turn generate
the following SAT/CNF encoding:

```TODO: list here```

Each delivery+time unit pairing is separately enumerated; the
total number of possible but infeasible pairs is reported as (aggregate)
```CONFLICTS```.

Note that we do not collapse consecutive units into larger ranges; this
wasteful encoding seems to be reasonable given our current SAT solvers.
*Evaluating everything at a unit granularity allows us to accommodate
essentially arbitrarily fragmented delivery schedues.*

