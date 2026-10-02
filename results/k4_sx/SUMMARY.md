# proof/k4-sx: summed counters

Made by `python3 k4/sx_summary.py` from the complete logs under `results/k4_sx/`. Every log starts with the command that wrote it.

## Hunts for non-completable f = 1 keys (k4/sx_hunt.py on k4/red.c)

### n3_all (6 logs)

- distinct profiles with a non-completable key: 62208
- f1: 7284544
- key_noncompletable: 62208
- keys: 14256832
- profiles: 299837376

### n4_2_r20k (1 logs)

- distinct profiles with a non-completable key: 0
- f1: 165045
- key_noncompletable: 0
- keys: 303564
- profiles: 6180000

### n4_3_r40k (1 logs)

- distinct profiles with a non-completable key: 59
- f1: 551666
- key_noncompletable: 59
- keys: 1044381
- profiles: 13560000

### n4_pure_r400k (1 logs)

- distinct profiles with a non-completable key: 2347
- f1: 4310853
- key_noncompletable: 2363
- keys: 8443995
- profiles: 87600000

### n4_pure_r40k (1 logs)

- distinct profiles with a non-completable key: 240
- f1: 430765
- key_noncompletable: 240
- keys: 844132
- profiles: 8760000

### n5_n4_2_r200 (1 logs)

- distinct profiles with a non-completable key: 0
- f1: 10719
- key_noncompletable: 0
- keys: 19971
- profiles: 1093600

### n5_n4_3_r200 (5 logs)

- distinct profiles with a non-completable key: 0
- f1: 51240
- key_noncompletable: 0
- keys: 96226
- profiles: 1972200

### n5_n4_4_r200 (5 logs)

- distinct profiles with a non-completable key: 0
- f1: 82386
- key_noncompletable: 0
- keys: 157244
- profiles: 1969200

### n5_pure_r1000 (5 logs)

- distinct profiles with a non-completable key: 11
- f1: 263852
- key_noncompletable: 11
- keys: 516100
- profiles: 4674000

### total

- distinct profiles with a non-completable key: 64865
- f1: 13151070
- key_noncompletable: 64881
- keys: 25682445
- profiles: 425646376

## Repair lemmas at the Z′-maxima of the non-completable f = 1 keys (k4/sx_zprime.py)

### n3_all (17 logs)

- MAIN CASE A: 104372
- MAIN CASE B1: 7824
- MAIN CASE C: 4052
- Zmax: 116248
- keys: 62208
- keys xtype=BT: 14880
- keys xtype=bc: 5072
- keys xtype=bcbd: 13264
- keys xtype=flat: 28992
- regime I: 108424
- regime I GPM ok k=1 adjacent(T3)=True: 25440
- regime I GPM paths k=1 leaf kind=Tg: 25440
- regime I OS o theta-b=False: 131448
- regime I OS o theta-b=True: 27944
- regime I OS succeeds: 108424
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 1200
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 5792
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 17392
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 1992
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 1568
- regime I Prop C applies=False (only (H) missing=False): 85972
- regime I Prop C applies=True (only (H) missing=False): 22452
- regime I Prop C' applies=False (only (H') missing=False): 85428
- regime I Prop C' applies=True (only (H') missing=False): 22996
- regime I Zmax with a direct T3 move: 108424
- regime I cases A*,C,C': 4052
- regime I cases A,A*: 59092
- regime I cases A,A*,B1: 25440
- regime I cases A,A*,C: 896
- regime I cases A,A*,C': 1440
- regime I cases A,A*,C,C': 17504
- regime I direct kind ('zT', '-', 'own=V'): 6240
- regime I direct kind ('zT', '-', 'own=x'): 18720
- regime I direct kind ('zT', 'hV', 'own=V'): 12640
- regime I direct kind ('zT', 'hV', 'own=x'): 24800
- regime I direct kind ('zV', '-', 'own=V'): 30744
- regime I direct kind ('zV', '-', 'own=other'): 12640
- regime I direct kind ('zV', '-', 'own=x'): 103012
- regime I direct kind ('zV', 'h', 'own=other'): 13440
- regime I direct kind ('zV', 'h', 'own=x'): 44304
- regime I direct kind ('zV', 'hV', 'own=V'): 32384
- regime I direct kind ('zV', 'hV', 'own=x'): 56632
- regime I |V|=1 |T|=1 |VT|=1 t=0 x=BT: 25632
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bc: 13760
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bcbd: 9280
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=flat: 2400
- regime I |V|=2 |T|=1 |VT|=1 t=1 x=BT: 6384
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=bcbd: 7120
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 18012
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bc: 1960
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bcbd: 6520
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 17356
- regime II: 7824
- regime II GPM ok k=1 adjacent(T3)=True: 7824
- regime II GPM paths k=1 leaf kind=D: 6240
- regime II GPM paths k=1 leaf kind=R: 1584
- regime II OS succeeds: 0
- regime II Prop C applies=False (only (H) missing=False): 7824
- regime II Prop C' applies=False (only (H') missing=False): 7824
- regime II Zmax with a direct T3 move: 7824
- regime II cases B1: 7824
- regime II direct kind ('zT', '-', 'own=V'): 2160
- regime II direct kind ('zT', 'hV', 'own=V'): 1392
- regime II direct kind ('zT', 'hV', 'own=x'): 7824
- regime II |V|=1 |T|=1 |VT|=0 t=0 x=BT: 7824

### n4_3_r40k (1 logs)

- MAIN CASE A: 148
- MAIN CASE B1: 42
- MAIN CASE C': 1
- Zmax: 191
- keys: 59
- keys xtype=bcbd: 1
- keys xtype=flat: 58
- regime I: 191
- regime I GPM ok k=1 adjacent(T3)=True: 80
- regime I GPM paths k=1 leaf kind=R: 1
- regime I GPM paths k=1 leaf kind=R s in L: 2
- regime I GPM paths k=1 leaf kind=T3: 67
- regime I GPM paths k=1 leaf kind=Tg: 12
- regime I OS o theta-b=False: 195
- regime I OS o theta-b=True: 105
- regime I OS succeeds: 191
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 3
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 70
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 16
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 14
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 2
- regime I Prop B' (modified path move) k=1 works=True: 2
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=True: 2
- regime I Prop C applies=False (only (H) missing=False): 93
- regime I Prop C applies=True (only (H) missing=False): 98
- regime I Prop C' applies=False (only (H') missing=False): 187
- regime I Prop C' applies=False (only (H') missing=True): 2
- regime I Prop C' applies=True (only (H') missing=False): 2
- regime I Zmax with a direct T3 move: 191
- regime I cases A*,B1,C: 42
- regime I cases A*,C': 1
- regime I cases A,A*: 51
- regime I cases A,A*,B1: 38
- regime I cases A,A*,B1',Rs: 2
- regime I cases A,A*,C: 54
- regime I cases A,A*,C': 1
- regime I cases A,A*,C,C-H: 2
- regime I direct kind ('zT', '-', 'own=V'): 82
- regime I direct kind ('zT', '-', 'own=x'): 49
- regime I direct kind ('zT', 'hV', 'own=V'): 78
- regime I direct kind ('zT', 'hV', 'own=x'): 82
- regime I direct kind ('zV', '-', 'own=V'): 93
- regime I direct kind ('zV', '-', 'own=other'): 12
- regime I direct kind ('zV', '-', 'own=x'): 182
- regime I direct kind ('zV', 'h', 'own=V'): 67
- regime I direct kind ('zV', 'h', 'own=other'): 12
- regime I direct kind ('zV', 'h', 'own=x'): 51
- regime I direct kind ('zV', 'hV', 'own=V'): 96
- regime I direct kind ('zV', 'hV', 'own=other'): 4
- regime I direct kind ('zV', 'hV', 'own=x'): 119
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 50
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 32
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 38
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 29
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 3
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 39

### n4_pure_r400k (1 logs)

- MAIN CASE A: 3390
- MAIN CASE B1: 135
- MAIN CASE B1': 12
- MAIN CASE C: 73
- MAIN CASE C': 30
- MAIN CASE rest: 5
- Zmax: 3645
- keys: 2362
- keys xtype=bc: 89
- keys xtype=bcbd: 250
- keys xtype=flat: 2023
- regime I: 3627
- regime I GPM ok k=1 adjacent(T3)=True: 464
- regime I GPM paths k=1 leaf kind=D: 23
- regime I GPM paths k=1 leaf kind=R: 17
- regime I GPM paths k=1 leaf kind=R s in L: 33
- regime I GPM paths k=1 leaf kind=T4: 19
- regime I GPM paths k=1 leaf kind=Tg: 405
- regime I OS o theta-b=False: 4829
- regime I OS o theta-b=True: 2092
- regime I OS succeeds: 3623
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 45
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 118
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 381
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 407
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 5 (omega+2=6), T=several: 825
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 160
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 68
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=6), T=several: 88
- regime I Prop B' (modified path move) k=1 works=False: 2
- regime I Prop B' (modified path move) k=1 works=True: 31
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=False: 33
- regime I Prop C applies=False (only (H) missing=False): 2089
- regime I Prop C applies=False (only (H) missing=True): 31
- regime I Prop C applies=True (only (H) missing=False): 1507
- regime I Prop C' applies=False (only (H') missing=False): 3268
- regime I Prop C' applies=False (only (H') missing=True): 55
- regime I Prop C' applies=True (only (H') missing=False): 304
- regime I Zmax with a direct T3 move: 3627
- regime I cases A*,B1,C: 128
- regime I cases A*,B1,C-H: 1
- regime I cases A*,C: 5
- regime I cases A*,C': 29
- regime I cases A*,C,C': 63
- regime I cases A*,C,C',C-H: 5
- regime I cases A*,C-H,Rs: 2
- regime I cases A,A*: 1558
- regime I cases A,A*,B1: 287
- regime I cases A,A*,B1,C: 40
- regime I cases A,A*,B1,Rs: 8
- regime I cases A,A*,C: 1172
- regime I cases A,A*,C': 183
- regime I cases A,A*,C',C-H: 7
- regime I cases A,A*,C,C',C-H: 16
- regime I cases A,A*,C,C-H: 78
- regime I cases A,A*,C-H: 21
- regime I cases A,A*,Rs: 20
- regime I cases C': 1
- regime I cases Rs: 3
- regime I direct kind ('zT', '-', 'own=V'): 319
- regime I direct kind ('zT', '-', 'own=x'): 340
- regime I direct kind ('zT', 'hV', 'own=V'): 303
- regime I direct kind ('zT', 'hV', 'own=x'): 486
- regime I direct kind ('zV', '-', 'own=V'): 2630
- regime I direct kind ('zV', '-', 'own=other'): 30
- regime I direct kind ('zV', '-', 'own=x'): 3213
- regime I direct kind ('zV', 'h', 'own=V'): 692
- regime I direct kind ('zV', 'h', 'own=other'): 41
- regime I direct kind ('zV', 'h', 'own=x'): 792
- regime I direct kind ('zV', 'hV', 'own=V'): 2965
- regime I direct kind ('zV', 'hV', 'own=other'): 56
- regime I direct kind ('zV', 'hV', 'own=x'): 3337
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 211
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 188
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 312
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 353
- regime I |V|=2 |T|=3 |VT|=2 t=0 x=flat: 38
- regime I |V|=2 |T|=3 |VT|=2 t=1 x=flat: 52
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bc: 122
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 333
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 1952
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=bc: 6
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=flat: 60
- regime II: 18
- regime II GPM ok k=1 adjacent(T3)=True: 6
- regime II GPM ok k=2 adjacent(T3)=True: 6
- regime II GPM paths k=1 leaf kind=R: 6
- regime II GPM paths k=1 leaf kind=R s in L: 12
- regime II GPM paths k=2 leaf kind=R: 6
- regime II GPM paths k=2 leaf kind=R s in L: 12
- regime II OS succeeds: 0
- regime II Prop B' (modified path move) k=1 works=True: 12
- regime II Prop B' (modified path move) k=2 works=True: 12
- regime II Prop B' k=1 hypothesis (y valued only by x) holds=True: 12
- regime II Prop B' k=2 hypothesis (y valued only by x) holds=True: 12
- regime II Prop C applies=False (only (H) missing=False): 18
- regime II Prop C' applies=False (only (H') missing=False): 18
- regime II Zmax with a direct T3 move: 18
- regime II cases B1',Bk',Rs: 12
- regime II cases B1,Bk-adj: 6
- regime II direct kind ('zT', '-', 'own=V'): 12
- regime II direct kind ('zT', '-', 'own=x'): 12
- regime II direct kind ('zT', 'h', 'own=V'): 12
- regime II direct kind ('zT', 'h', 'own=x'): 12
- regime II direct kind ('zT', 'hV', 'own=V'): 18
- regime II direct kind ('zT', 'hV', 'own=other'): 18
- regime II direct kind ('zT', 'hV', 'own=x'): 18
- regime II |V|=1 |T|=2 |VT|=0 t=0 x=bcbd: 18

### n4_pure_r40k (1 logs)

- MAIN CASE A: 346
- MAIN CASE B1: 16
- MAIN CASE B1': 6
- MAIN CASE C: 5
- MAIN CASE C': 1
- Zmax: 374
- keys: 240
- keys xtype=bc: 11
- keys xtype=bcbd: 30
- keys xtype=flat: 199
- regime I: 362
- regime I GPM ok k=1 adjacent(T3)=True: 40
- regime I GPM ok k=2 adjacent(T3)=True: 4
- regime I GPM paths k=1 leaf kind=D: 7
- regime I GPM paths k=1 leaf kind=R: 3
- regime I GPM paths k=1 leaf kind=R s in L: 2
- regime I GPM paths k=1 leaf kind=T4: 2
- regime I GPM paths k=1 leaf kind=Tg: 28
- regime I GPM paths k=2 leaf kind=Tg: 4
- regime I OS o theta-b=False: 485
- regime I OS o theta-b=True: 205
- regime I OS succeeds: 361
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 6
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 7
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 34
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 45
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 5 (omega+2=6), T=several: 82
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 16
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 6
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=6), T=several: 9
- regime I Prop B' (modified path move) k=1 works=True: 2
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=False: 2
- regime I Prop C applies=False (only (H) missing=False): 205
- regime I Prop C applies=False (only (H) missing=True): 1
- regime I Prop C applies=True (only (H) missing=False): 156
- regime I Prop C' applies=False (only (H') missing=False): 335
- regime I Prop C' applies=False (only (H') missing=True): 3
- regime I Prop C' applies=True (only (H') missing=False): 24
- regime I Zmax with a direct T3 move: 362
- regime I cases A*,B1,C: 9
- regime I cases A*,C': 1
- regime I cases A*,C,C': 4
- regime I cases A*,C,C',C-H: 1
- regime I cases A,A*: 155
- regime I cases A,A*,B1: 26
- regime I cases A,A*,B1,C: 4
- regime I cases A,A*,Bk-adj: 4
- regime I cases A,A*,C: 131
- regime I cases A,A*,C': 16
- regime I cases A,A*,C,C',C-H: 2
- regime I cases A,A*,C,C-H: 5
- regime I cases A,A*,C-H: 1
- regime I cases A,A*,Rs: 2
- regime I cases B1: 1
- regime I direct kind ('zT', '-', 'own=V'): 25
- regime I direct kind ('zT', '-', 'own=x'): 28
- regime I direct kind ('zT', 'h', 'own=V'): 4
- regime I direct kind ('zT', 'h', 'own=other'): 4
- regime I direct kind ('zT', 'h', 'own=x'): 4
- regime I direct kind ('zT', 'hV', 'own=V'): 30
- regime I direct kind ('zT', 'hV', 'own=x'): 39
- regime I direct kind ('zV', '-', 'own=V'): 273
- regime I direct kind ('zV', '-', 'own=x'): 319
- regime I direct kind ('zV', 'h', 'own=V'): 71
- regime I direct kind ('zV', 'h', 'own=other'): 2
- regime I direct kind ('zV', 'h', 'own=x'): 86
- regime I direct kind ('zV', 'hV', 'own=V'): 296
- regime I direct kind ('zV', 'hV', 'own=other'): 9
- regime I direct kind ('zV', 'hV', 'own=x'): 335
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=flat: 4
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 8
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 24
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 40
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 37
- regime I |V|=2 |T|=3 |VT|=2 t=0 x=flat: 4
- regime I |V|=2 |T|=3 |VT|=2 t=1 x=flat: 6
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bc: 15
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 36
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 186
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=flat: 2
- regime II: 12
- regime II GPM ok k=1 adjacent(T3)=True: 6
- regime II GPM ok k=2 adjacent(T3)=True: 6
- regime II GPM paths k=1 leaf kind=R: 6
- regime II GPM paths k=1 leaf kind=R s in L: 6
- regime II GPM paths k=2 leaf kind=R: 6
- regime II GPM paths k=2 leaf kind=R s in L: 6
- regime II OS succeeds: 0
- regime II Prop B' (modified path move) k=1 works=True: 6
- regime II Prop B' (modified path move) k=2 works=True: 6
- regime II Prop B' k=1 hypothesis (y valued only by x) holds=True: 6
- regime II Prop B' k=2 hypothesis (y valued only by x) holds=True: 6
- regime II Prop C applies=False (only (H) missing=False): 12
- regime II Prop C' applies=False (only (H') missing=False): 12
- regime II Zmax with a direct T3 move: 12
- regime II cases B1',Bk',Rs: 6
- regime II cases B1,Bk-adj: 6
- regime II direct kind ('zT', '-', 'own=V'): 8
- regime II direct kind ('zT', '-', 'own=x'): 8
- regime II direct kind ('zT', 'h', 'own=V'): 8
- regime II direct kind ('zT', 'h', 'own=x'): 8
- regime II direct kind ('zT', 'hV', 'own=V'): 4
- regime II direct kind ('zT', 'hV', 'own=other'): 12
- regime II direct kind ('zT', 'hV', 'own=x'): 12
- regime II |V|=1 |T|=2 |VT|=0 t=0 x=bcbd: 12

### n5_pure_r1000 (2 logs)

- MAIN CASE A: 13
- Zmax: 13
- keys: 11
- keys xtype=bcbd: 2
- keys xtype=flat: 9
- regime I: 13
- regime I GPM ok k=1 adjacent(T3)=True: 4
- regime I GPM paths k=1 leaf kind=R: 1
- regime I GPM paths k=1 leaf kind=Tg: 3
- regime I OS o theta-b=False: 21
- regime I OS o theta-b=True: 1
- regime I OS succeeds: 13
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 1
- regime I Prop C applies=False (only (H) missing=False): 13
- regime I Prop C' applies=False (only (H') missing=False): 12
- regime I Prop C' applies=True (only (H') missing=False): 1
- regime I Zmax with a direct T3 move: 13
- regime I cases A,A*: 8
- regime I cases A,A*,B1: 4
- regime I cases A,A*,C': 1
- regime I direct kind ('zT', '-', 'own=V'): 4
- regime I direct kind ('zT', '-', 'own=x'): 3
- regime I direct kind ('zT', 'hV', 'own=V'): 4
- regime I direct kind ('zT', 'hV', 'own=x'): 4
- regime I direct kind ('zV', '-', 'own=V'): 8
- regime I direct kind ('zV', '-', 'own=x'): 13
- regime I direct kind ('zV', 'hV', 'own=V'): 9
- regime I direct kind ('zV', 'hV', 'own=x'): 13
- regime I |V|=3 |T|=2 |VT|=1 t=1 x=flat: 4
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=bcbd: 2
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=flat: 7

### total

- MAIN CASE A: 108269
- MAIN CASE B1: 8017
- MAIN CASE B1': 18
- MAIN CASE C: 4130
- MAIN CASE C': 32
- MAIN CASE rest: 5
- Zmax: 120471
- keys: 64880
- keys xtype=BT: 14880
- keys xtype=bc: 5172
- keys xtype=bcbd: 13547
- keys xtype=flat: 31281
- regime I: 112617
- regime I GPM ok k=1 adjacent(T3)=True: 26028
- regime I GPM ok k=2 adjacent(T3)=True: 4
- regime I GPM paths k=1 leaf kind=D: 30
- regime I GPM paths k=1 leaf kind=R: 22
- regime I GPM paths k=1 leaf kind=R s in L: 37
- regime I GPM paths k=1 leaf kind=T3: 67
- regime I GPM paths k=1 leaf kind=T4: 21
- regime I GPM paths k=1 leaf kind=Tg: 25888
- regime I GPM paths k=2 leaf kind=Tg: 4
- regime I OS o theta-b=False: 136978
- regime I OS o theta-b=True: 30347
- regime I OS succeeds: 112612
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 4 (omega+2=5), T=several: 1254
- regime I OS theta-b: exact def(P')<def* False, OSd bundle value 5 (omega+2=6), T=several: 126
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 3 (omega+2=4), T=several: 6277
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 4 (omega+2=5), T=several: 17860
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value 5 (omega+2=6), T=several: 907
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=4), T=several: 2182
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=5), T=several: 1644
- regime I OS theta-b: exact def(P')<def* True, OSd bundle value None (omega+2=6), T=several: 97
- regime I Prop B' (modified path move) k=1 works=False: 2
- regime I Prop B' (modified path move) k=1 works=True: 35
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=False: 35
- regime I Prop B' k=1 hypothesis (y valued only by x) holds=True: 2
- regime I Prop C applies=False (only (H) missing=False): 88372
- regime I Prop C applies=False (only (H) missing=True): 32
- regime I Prop C applies=True (only (H) missing=False): 24213
- regime I Prop C' applies=False (only (H') missing=False): 89230
- regime I Prop C' applies=False (only (H') missing=True): 60
- regime I Prop C' applies=True (only (H') missing=False): 23327
- regime I Zmax with a direct T3 move: 112617
- regime I cases A*,B1,C: 179
- regime I cases A*,B1,C-H: 1
- regime I cases A*,C: 5
- regime I cases A*,C': 31
- regime I cases A*,C,C': 4119
- regime I cases A*,C,C',C-H: 6
- regime I cases A*,C-H,Rs: 2
- regime I cases A,A*: 60864
- regime I cases A,A*,B1: 25795
- regime I cases A,A*,B1',Rs: 2
- regime I cases A,A*,B1,C: 44
- regime I cases A,A*,B1,Rs: 8
- regime I cases A,A*,Bk-adj: 4
- regime I cases A,A*,C: 2253
- regime I cases A,A*,C': 1641
- regime I cases A,A*,C',C-H: 7
- regime I cases A,A*,C,C': 17504
- regime I cases A,A*,C,C',C-H: 18
- regime I cases A,A*,C,C-H: 85
- regime I cases A,A*,C-H: 22
- regime I cases A,A*,Rs: 22
- regime I cases B1: 1
- regime I cases C': 1
- regime I cases Rs: 3
- regime I direct kind ('zT', '-', 'own=V'): 6670
- regime I direct kind ('zT', '-', 'own=x'): 19140
- regime I direct kind ('zT', 'h', 'own=V'): 4
- regime I direct kind ('zT', 'h', 'own=other'): 4
- regime I direct kind ('zT', 'h', 'own=x'): 4
- regime I direct kind ('zT', 'hV', 'own=V'): 13055
- regime I direct kind ('zT', 'hV', 'own=x'): 25411
- regime I direct kind ('zV', '-', 'own=V'): 33748
- regime I direct kind ('zV', '-', 'own=other'): 12682
- regime I direct kind ('zV', '-', 'own=x'): 106739
- regime I direct kind ('zV', 'h', 'own=V'): 830
- regime I direct kind ('zV', 'h', 'own=other'): 13495
- regime I direct kind ('zV', 'h', 'own=x'): 45233
- regime I direct kind ('zV', 'hV', 'own=V'): 35750
- regime I direct kind ('zV', 'hV', 'own=other'): 69
- regime I direct kind ('zV', 'hV', 'own=x'): 60436
- regime I |V|=1 |T|=1 |VT|=1 t=0 x=BT: 25632
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bc: 13760
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=bcbd: 9280
- regime I |V|=1 |T|=2 |VT|=1 t=0 x=flat: 2404
- regime I |V|=2 |T|=1 |VT|=1 t=1 x=BT: 6384
- regime I |V|=2 |T|=2 |VT|=1 t=0 x=flat: 269
- regime I |V|=2 |T|=2 |VT|=1 t=1 x=flat: 244
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=bcbd: 7120
- regime I |V|=2 |T|=2 |VT|=2 t=0 x=flat: 18402
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bc: 1960
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=bcbd: 6520
- regime I |V|=2 |T|=2 |VT|=2 t=1 x=flat: 17775
- regime I |V|=2 |T|=3 |VT|=2 t=0 x=flat: 42
- regime I |V|=2 |T|=3 |VT|=2 t=1 x=flat: 58
- regime I |V|=3 |T|=2 |VT|=1 t=1 x=flat: 4
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bc: 137
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=bcbd: 372
- regime I |V|=3 |T|=2 |VT|=2 t=1 x=flat: 2177
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=bc: 6
- regime I |V|=3 |T|=3 |VT|=3 t=1 x=flat: 62
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=bcbd: 2
- regime I |V|=4 |T|=2 |VT|=2 t=1 x=flat: 7
- regime II: 7854
- regime II GPM ok k=1 adjacent(T3)=True: 7836
- regime II GPM ok k=2 adjacent(T3)=True: 12
- regime II GPM paths k=1 leaf kind=D: 6240
- regime II GPM paths k=1 leaf kind=R: 1596
- regime II GPM paths k=1 leaf kind=R s in L: 18
- regime II GPM paths k=2 leaf kind=R: 12
- regime II GPM paths k=2 leaf kind=R s in L: 18
- regime II OS succeeds: 0
- regime II Prop B' (modified path move) k=1 works=True: 18
- regime II Prop B' (modified path move) k=2 works=True: 18
- regime II Prop B' k=1 hypothesis (y valued only by x) holds=True: 18
- regime II Prop B' k=2 hypothesis (y valued only by x) holds=True: 18
- regime II Prop C applies=False (only (H) missing=False): 7854
- regime II Prop C' applies=False (only (H') missing=False): 7854
- regime II Zmax with a direct T3 move: 7854
- regime II cases B1: 7824
- regime II cases B1',Bk',Rs: 18
- regime II cases B1,Bk-adj: 12
- regime II direct kind ('zT', '-', 'own=V'): 2180
- regime II direct kind ('zT', '-', 'own=x'): 20
- regime II direct kind ('zT', 'h', 'own=V'): 20
- regime II direct kind ('zT', 'h', 'own=x'): 20
- regime II direct kind ('zT', 'hV', 'own=V'): 1414
- regime II direct kind ('zT', 'hV', 'own=other'): 30
- regime II direct kind ('zT', 'hV', 'own=x'): 7854
- regime II |V|=1 |T|=1 |VT|=0 t=0 x=BT: 7824
- regime II |V|=1 |T|=2 |VT|=0 t=0 x=bcbd: 30

## Lemma A⁺ at f ≥ 2 (k4/sx_f2.py)

### catalogues_f2 (1 logs)

- A+ applies, chain length j=0: 31
- A+ applies, chain length j=1: 2
- A+ chain found but theta fails: 37
- B+ applies, chain j=0, path k=1: 8
- Zmax: 110
- Zmax: Lemma A+ applies=False: 77
- Zmax: Lemma A+ applies=True: 33
- Zmax: Lemma A+ or B+ applies=False: 77
- Zmax: Lemma A+ or B+ applies=True: 33
- Zmax: Lemma B+ applies=False: 102
- Zmax: Lemma B+ applies=True: 8
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 108
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=True: 2
- Zmax: free-valid owner exists=True: 110
- free-valid owner: frozen agents threatened=1: 131
- free-valid owner: frozen agents threatened=2: 61
- keys f=2: 67
- keys: Lemma A+ or B+ at some Zmax=False: 49
- keys: Lemma A+ or B+ at some Zmax=True: 18
- no A+/B+: a needer on the path, but theta fails or an (R) leaf with s in L: 18
- no A+/B+: leaf threatens 2 frozen agents: 45
- no A+/B+: the free needers are off the path to the leaf: 25
- profiles f=2: 65

### keys_rt4_n5b (1 logs)

- DLK_T3 FAIL f=3: 2
- DLK_T3T4 FAIL f=3: 2
- SKG_T3 fail f=3: 2
- SKG_T3T4 fail f=3: 2
- keys def*>0 f=3: 15
- keys f=3: 35
- keys f=3 def*=-1: 20
- keys f=3 def*=1: 15
- profiles: 2
- profiles f=3: 2
- profiles f>=1, omega>=1: 2
- profiles with a key def*>0 f=3: 2

### keys_rt4_n5c (1 logs)

- DLK_T3 FAIL f=3: 8
- DLK_T3T4 FAIL f=3: 8
- SKG_T3 fail f=3: 8
- SKG_T3T4 fail f=3: 8
- keys def*>0 f=3: 26
- keys f=3: 74
- keys f=3 def*=-1: 36
- keys f=3 def*=0: 12
- keys f=3 def*=1: 26
- profiles: 8
- profiles f=3: 8
- profiles f>=1, omega>=1: 8
- profiles with a key def*>0 f=3: 8

### rt4_n5b (1 logs)

- A+ applies, chain length j=0: 24
- A+ applies, chain length j=1: 57
- Zmax: 81
- Zmax: Lemma A+ applies=True: 81
- Zmax: Lemma A+ or B+ applies=True: 81
- Zmax: Lemma B+ applies=False: 81
- Zmax: direct T3 move=False, direct T3+ move=True, direct T4 move=False: 15
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 66
- Zmax: free-valid owner exists=True: 81
- free-valid owner: frozen agents threatened=1: 162
- keys f=3: 15
- keys: Lemma A+ or B+ at some Zmax=True: 15
- profiles f=3: 2

### rt4_n5c (1 logs)

- A+ applies, chain length j=0: 54
- A+ applies, chain length j=1: 32
- A+ chain found but theta fails: 35
- B+ applies, chain j=1, path k=1: 28
- Zmax: 118
- Zmax: Lemma A+ applies=False: 32
- Zmax: Lemma A+ applies=True: 86
- Zmax: Lemma A+ or B+ applies=False: 32
- Zmax: Lemma A+ or B+ applies=True: 86
- Zmax: Lemma B+ applies=False: 90
- Zmax: Lemma B+ applies=True: 28
- Zmax: direct T3 move=False, direct T3+ move=True, direct T4 move=False: 25
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 93
- Zmax: free-valid owner exists=True: 118
- free-valid owner: frozen agents threatened=1: 173
- free-valid owner: frozen agents threatened=2: 35
- keys f=3: 26
- keys: Lemma A+ or B+ at some Zmax=False: 7
- keys: Lemma A+ or B+ at some Zmax=True: 19
- profiles f=3: 8

### total

- A+ applies, chain length j=0: 109
- A+ applies, chain length j=1: 91
- A+ chain found but theta fails: 72
- B+ applies, chain j=0, path k=1: 8
- B+ applies, chain j=1, path k=1: 28
- DLK_T3 FAIL f=3: 10
- DLK_T3T4 FAIL f=3: 10
- SKG_T3 fail f=3: 10
- SKG_T3T4 fail f=3: 10
- Zmax: 309
- Zmax: Lemma A+ applies=False: 109
- Zmax: Lemma A+ applies=True: 200
- Zmax: Lemma A+ or B+ applies=False: 109
- Zmax: Lemma A+ or B+ applies=True: 200
- Zmax: Lemma B+ applies=False: 273
- Zmax: Lemma B+ applies=True: 36
- Zmax: direct T3 move=False, direct T3+ move=True, direct T4 move=False: 40
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=False: 267
- Zmax: direct T3 move=True, direct T3+ move=True, direct T4 move=True: 2
- Zmax: free-valid owner exists=True: 309
- free-valid owner: frozen agents threatened=1: 466
- free-valid owner: frozen agents threatened=2: 96
- keys def*>0 f=3: 41
- keys f=2: 67
- keys f=3: 150
- keys f=3 def*=-1: 56
- keys f=3 def*=0: 12
- keys f=3 def*=1: 41
- keys: Lemma A+ or B+ at some Zmax=False: 56
- keys: Lemma A+ or B+ at some Zmax=True: 52
- no A+/B+: a needer on the path, but theta fails or an (R) leaf with s in L: 18
- no A+/B+: leaf threatens 2 frozen agents: 45
- no A+/B+: the free needers are off the path to the leaf: 25
- profiles: 10
- profiles f=2: 65
- profiles f=3: 20
- profiles f>=1, omega>=1: 10
- profiles with a key def*>0 f=3: 10

