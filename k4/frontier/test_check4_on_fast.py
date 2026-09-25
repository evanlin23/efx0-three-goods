"""Run main's sensitivity test k4/test_check4.py (unchanged) against k4/check4_fast.py instead of k4/check4.py: the
n = 3 certificate passes and each corruption (a dropped m group, a non-D2 allocation, malformed allocations, a deleted
allocation, a deleted core, a wrong --expect) is rejected. Usage: test_check4_on_fast.py"""
import os, runpy, sys
K4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, K4)
import check4_fast
sys.modules['check4'] = check4_fast          # test_check4.py's "import check4" now gets the fast checker
print("k4/test_check4.py run with check4 = k4/check4_fast.py", flush=True)
runpy.run_path(os.path.join(K4, 'test_check4.py'), run_name='__main__')
