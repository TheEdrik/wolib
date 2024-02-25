#!/usr/bin/python3

import pstats

p = pstats.Stats('profile.log')
p.sort_stats('cumulative').print_stats(30)

