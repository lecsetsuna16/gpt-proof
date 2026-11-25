"""Draw the two exact periodic cells; the image is explanatory, not a proof."""
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch

out = Path(__file__).resolve().parent
plt.rcParams.update({"font.family": "DejaVu Sans", "mathtext.fontset": "dejavusans"})
fig, ax = plt.subplots(figsize=(12, 5.8), dpi=180)
fig.patch.set_facecolor("#f7f8fa")
ax.set_facecolor("#f7f8fa")
ax.set_xlim(-0.65, 4.65)
ax.set_ylim(-0.72, 2.55)
ax.axis("off")
blue, red, ink, gray = "#2761bd", "#cf5a43", "#172b46", "#7b8799"
fig.text(.065, .94, "A repulsive collision barrier does not force uniform spacing",
         fontsize=17, color=ink, weight="bold")
fig.text(.065, .885, r"$V_{\sigma\tau}(r)=\lambda/r^2-\sigma\tau\,4/(4+r^2)$"
         r"   |   $0<\lambda\leq 1/1000$", fontsize=14, color=ink)

def row(y, coords, name, gap_labels):
    ax.plot([0, 4], [y, y], color="#c4cbd6", linewidth=2, zorder=0)
    ax.text(-.6, y+.13, name, fontsize=16, weight="bold", color=ink)
    for j, x in enumerate(coords + [4]):
        ghost = j == 4
        color = blue if j % 2 == 0 else red
        ax.scatter([x], [y], s=580, color=color, alpha=.28 if ghost else 1,
                   edgecolors="#ffffff", linewidths=2, zorder=3)
        ax.text(x, y, "+" if j % 2 == 0 else "−", color="white",
                fontsize=20, ha="center", va="center", weight="bold", zorder=4)
        label = {0:"0", 1:"1", 1.5:r"$3/2$", 2:"2", 2.5:r"$5/2$", 3:"3", 4:"4"}[x]
        ax.text(x, y+.25, label, fontsize=13, color=ink, ha="center")
    for left, right, label in zip(coords, coords[1:] + [4], gap_labels):
        ax.add_patch(FancyArrowPatch((left, y-.29), (right, y-.29),
                    arrowstyle="|-|", mutation_scale=8, color=gray, linewidth=1.2))
        ax.text((left+right)/2, y-.44, label, fontsize=12, color=gray, ha="center")

row(1.57, [0,1,2,3], "U", ["1", "1", "1", "1"])
row(.42, [0,1.5,2,2.5], "X", [r"$3/2$", r"$1/2$", r"$1/2$", r"$3/2$"])
ax.plot([4,4], [.12,1.85], color=gray, linestyle=(0,(3,4)), linewidth=1)
ax.text(4.11, 1.0, "next\nperiod", color=gray, fontsize=11, va="center")
fig.text(.065, .085, "Same density. Same alternating species. Every periodic image included.",
         fontsize=12, color=ink)
fig.text(.065, .035, r"Lean-certified:  $E(U)-E(X)>1/32$"
         "   (ordered-pair convention; conventional energy gap > 1/64)",
         fontsize=12, color=ink, weight="bold")
fig.savefig(out / "chain_geometry.png", facecolor=fig.get_facecolor(), bbox_inches="tight")
plt.close(fig)
