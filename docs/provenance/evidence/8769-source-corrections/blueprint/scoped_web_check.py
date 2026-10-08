import sys
from pathlib import Path
sys.path.insert(0, '/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-corrections/scripts')
import test_tenkz_equation_web as equations
import test_blueprint_web_render as render
root = Path('/var/folders/d1/qpfb8kqs3dj482nzfg_0yvkc0000gn/T/tnlean-source-corrections-blueprint-35ahwqev/blueprint/web')
equations.PAGES = tuple(p.name for p in sorted(root.glob('*.html')))
sys.argv = ['test_blueprint_web_render.py', '--web-root', str(root), '--jobs', '1']
raise SystemExit(render.main())
