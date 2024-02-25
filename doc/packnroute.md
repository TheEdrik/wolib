# Pack-and-route plugin for ERP integration

Visegrady, Tamas ```<tamas@visegrady.ch>```

# Introduction

This document summarizes the data structures and algorithms used by an
ERP routing module, which assigns deliveries to a predefined set of
vehicles. In addition to implementation details, we describe constraints
we impose on the ERP module calling our library.

# Vehicle routing problem

The Vehicle Routing Problem (VRP) is a well-studied optimization
problem. While significant theoretical literature exists, practical
implementations use a diverse set of heuristics. We document the set of
heuristics which have been selected for our implementation, and the
restrictions we impose on applications integrating our library.

In practice, one encounters a wide range of definitions of VRP types.
Without referencing specific literature, we consider the following
features critical:

    1. Allow scaling to single-pass processing of up to single-digit
    thousand deliveries under reasonable time constraints. We implicitly
    assume the system is capable of dealing with a suitable number of
    vehicles.

    2. Allow essentially arbitrary restrictions on delivery windows.
    Specifically, do not restrict deliveries to a single window, or even
    windows of uniform size. (Practically, we assign deliveries into
    quantized time units---of a few minutes, currently---and windows are
    simply arbitrary collections of those.)

    3. Assume no or minimal variation in vehicle capability. Allow
    assignments to one or possibly a few discrete vehicle types, but do not
    target vehicle-granular types.

    4. Prefer approximation algorithms, or their close derivatives, which
    terminate in not more than quadratic time, and low constants. For
    problem sizes we are interested in, we effectively expect to obtain
    solutions in seconds.

    5. Allow *routing and scheduling arbitrary mixtures of still
    flexible and already processed deliveries* and vehicle assignments.
    This flexibility *allows us to operate our solver to operate
    incrementally*---and conversely, to interrupt searching for a
    solution at arbitrary steps.

    6. *Use a SAT solver* as the preferred tool *for NP-complete
    approximations* which we do not implement ourselves. (As a
    consequence, we formulate all constituent problems as natively
    solvable and as SAT problems as well.) *Consider seamless
    integration of SAT and local solutions* by allowing only subproblems
    to be pased to the SAT solver, if necessary.

    Using only SAT solvers as an external tool, we expect to be able
    to scale essentially arbitrarily, including cloud-based solvers.
    (Our local instances will incorporate one of the resource-friendly
    solvers.)


# Time representation

We use a mixed representation to mark the flow of time; both scales
are discrete---with different representations---and they represent
the inherently quantized nature of deliveries. We primarily mark
*time-of-day with a resolution of minutes* as our fundamental index of
time. A quantized representation, collapsing ```M```-minute windows into
*time units* serves as a coarse reduction of complexity. The granularity
of time units represents some of the inherent uncertainty of deliveries.

Given the nature and uncertainties inherent in routing, *we consider
time windows of 5, 10, or 15 minutes.* We consider a resolution higher
than 5 minutes unrealistic even for city-scaled delivery areas, and 15
still suitable for geographically-scaled routing. We consider delivery
approximations which create minute-resolution schedules inherently
flawed.

Our quantized representation feeds a number of bitmasks, since practical
(time) unit sizes collapse typical workdays into dozens of bits.
In other words, most time-related comparisons amount to Boolean
operations over word-sized bitmasks, even if our internal bookkeeping
uses minutes.

# Approximation of point-to-point traversal

We assume an offline-produced, map-based lookup table to provide
traversal-time estimates between arbitrary pairs of points.

## Offline map maintenance

We assume the coordinate-to-time mapping to be maintained offline, as a
static lookup table mapping pairs of coordinates to distances/delivery
times. We expect offline operations to update the mappings; our library
depends on static, unchanging estimates during the routing process.
(Temporal variation, such as accounting for peak traffic, is managed
entirely within our library.)

Since we approximate traversal times entirely within our routing loop,
*we do not depend on online calls to map pairs of coordinates to
expected traversal time*. In other words, while we acknowledge that
online traversal-estimation APIs may be available, we do not expect
our system to utilize them. We may start populating initial traversal
estimates using those APIs; however, with database growth, the number of
those offline calls is expected to diminish.

We assume an append-only table of coordinates, with continuous feedback
as deliveries are actually scheduled. (We do not consider the number of
deliveries prohibitive; we may need to revisit this assumptions if the
databases grow unreasonably large.) We expect that physical distance
may serve as a suitable initial approximation; one expects feedback to
override those initial estimates if vehicle feedback justifies it. *We
expect our distance-estimator database to evolve as a combination of
API-estimated and vehicle-experienced data.*

For each optimization pass, we expect a pre-filter to extract all point
pairs feasible for that collection of deliveries. For practical delivery
schedules not more than low thousands of thousands of deliveries, these
tables would need to store single-digit millions of distances/times,
which is not considered prohibitive.

## Peak periods

Our simplistic coordinate-derived distance/time approximation may
be easily extended to approximate the impact of peak periods. Since
our distance map is essentially coordinate-based---with possible
corrections---we add an additional correction factor, independent of the
map itself. We may approximate peak periods by adding 'zones' to the map
where slower traversal is to be expected.

One must note that *our delivery-enumerator loop*, in addition to
start/final coordinates, *is aware of the approximate time-of-day of
traversal* for each pair of points we consider for traversal. (In
other words, when we consider point pairs, we are also aware of the
approximate time of day when the point is to be traversed.) This
allows us to apply

Note that we believe that minute-granular, point-pair-specific
approximations of peak periods are fundamentally unreliable, without a
large database of past measurements.

=====================================================

While arrival and departure times are tracked in minutes, the coarser
units serve as initial filters, and conveniently, as a unit of
allocation. We currently assume that *no more than one delivery may be
mapped to a single unit.* The restriction might be relaxed later, but
some of our approximations---particularly, about timing slack around
deliveries---essentially prohibit completing more than one delivery per
unit per vehicle. (See separate description of how merged deliveries
would be still scheduled to complete within a single unit, if they are
in close physical proximity.)

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

4. For deliveries which have been assigned a vehicle, the ```dXX vNN```
combination MUST NOT be all-False. (The all-zero ```v0...vN``` counter
indicates no assigned vehicle.)

    The multi-bit vehicle-ID 'field' must also be lower than or equal to
    ```M``` when assigning ```M``` vehicles. (See separate note on
    range comparison.)

    Note that this restriction must change, once optionally scheduled
    deliveries are supported. In those cases, the vehicle ID is
    legitimately all-False if and only if no vehicle is assigned.

5. For conditions where multiple deliveries MUST NOT be assigned to
the same vehicle, one evaluates whether there is any difference in the
```v0...vN``` columns over the deliveries to check. (In other words,
for the first two deliveries, we must ensure that ```d0v0 d0v1``` and
```d1v0 d1v1``` are different values).

    Checking for differences across multi-bit fields is straightforward:
    calculate both ```AND``` and ```OR``` of the same set, and ensure
    these values are different. Due to their construction, the
    difference means ```AND(...)=0``` and ```OR(...)=1```, regardless of
    the number of bits checked. The aggregate then must check that at
    least one of the bits differs; this ensures not all of the multi-bit
    ```v0...vN``` values has been identical. (See example below.)

    If we allow optional deliveries, the all-0 vehicle ID is valid:
    it indicates that the delivery has no assigned vehicle (yet). The
    comparison is simply ORed with ```NOR(...)``` of the vehicle
    IDs which must tolerate not-yet-assigned vehicles. Following the
    previous example, ```NOR(d0v0 OR d0v1)``` is True when no vehicle
    has been assigned yet (both bits are ```0```).

# Fully expanded trivial example

A small delivery of two deliveries (d1, d2), not more than two vehicles
and therefore two vehicle bits (v1, v2), and a total of five available
time units (t0..t4) are considered. The following list of variables and
their Boolean expressions are considered:

```
d1t0'v0 d1t0'v1   ---------------   d1 may be delivered 0800-0859, inclusive
d1t1'v0 d1t1'v1   d2t1'v0 d2t1'v1   d2 may be delivered 0815-0914, inclusive
d1t2'v0 d1t2'v1   d2t2'v0 d2t2'v1
d1t3'v0 d1t3'v1   d2t3'v0 d2t3'v1
---------------   d2t4'v0 d2t4'v1
---------------------------------
d1v0    d1v1      d2v0    d2v1      --- derived variables: two-bit
                                    --- assigned-vehicle IDs
                                    --- d1v0 = OR(d1t0'v0 .. d1t3'v0) etc.
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
    Therefore, only one of the ```dXXtYYvNN``` combinations may not be
    all-```00```, and ```OR```ing the ```vNN``` "columns" trivially
    creates the summary variables. (The latter is useful to detect
    deliveries assigned to the same vehicle; see below.)

    For deliveries which have been assigned a vehicle, the ```dXXvNN```
    bits MAY NOT be all-zero. In other words, ```OR``` of these
    vehicle-ID bits for each ```dXX``` MUST be True.

6. if the two deliveries MUST NOT be assigned to the same vehicle, the
condensed two-bit ```dXXvNN``` IDs MUST differ (see example above). In
this example, we first form two 'columns' over ```v0``` and ```v1```,
and build expressions which are True if and only if there is at
least one bit difference within each 'column'. The ```OR``` of these
column-summarizing variables is True if and only if not all multi-bit
IDs are identical.

We build two 'columns' of two elements each: ```d1v0 d2v0``` and ```d1v1
d2v1```. If either ```(d1v0, d2v0)``` or ```(d1v1, d2v1)``` differ,
the values may not be all identical.

7. The conditions of not less than two time units' difference between
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

