import evaluation.failure_analysis as fa
import os
import json
import matplotlib.font_manager as fm

if os.path.exists("tasks/Baldur/minilang_errors.json"):
    (minilang_total, minilang_count, minilang_case_num) = json.load(open("tasks/Baldur/minilang_errors.json"))
else:
    minilang_count = {}
    minilang_total1, minilang_case_num1 = fa.analyze_failure(
        "tasks/Baldur/results/minilang-DS_pisa_result.db",
        "tasks/Baldur/results/minilang-DS_response.jsonl",
        "reasonwang/deepseek-prover-minilang",
        4022,
        minilang_count
    )

    minilang_total2, minilang_case_num2 = fa.analyze_failure(
        "tasks/Baldur/results/minilang_pisa_result.db",
        "tasks/Baldur/results/minilang_response.jsonl",
        "EleutherAI/llemma_7b",
        4022,
        minilang_count
    )

    minilang_total = minilang_total1 + minilang_total2
    minilang_case_num = minilang_case_num1 + minilang_case_num2
    print(minilang_total)
    with open("tasks/Baldur/minilang_errors.json", "w") as f:
        json.dump((minilang_total, minilang_count, minilang_case_num), f)

if os.path.exists("tasks/Baldur/isar_errors.json"):
    (isar_total, isar_count, isar_case_num) = json.load(open("tasks/Baldur/isar_errors.json"))
else:
    isar_count = {}
    isar_total1, isar_case_num1 = fa.analyze_failure(
        "tasks/Baldur/results/isar-SH*-DS_pisa_result.db",
        "tasks/Baldur/results/isar-SH*-DS_response.jsonl",
        "reasonwang/deepseek-prover-isar",
        4020,
        isar_count
    )

    isar_total2, isar_case_num2 = fa.analyze_failure(
        "tasks/Baldur/results/isar-SH*_pisa_result.db",
        "tasks/Baldur/results/isar-SH*_response.jsonl",
        "EleutherAI/llemma_7b",
        4020,
        isar_count
    )
    isar_total = isar_total1 + isar_total2
    isar_case_num = isar_case_num1 + isar_case_num2
    print(isar_total)
    with open("tasks/Baldur/isar_errors.json", "w") as f:
        json.dump((isar_total, isar_count, isar_case_num), f)


import numpy as np
import matplotlib.pyplot as plt

# 设置全局字体为 Times New Roman
plt.rcParams['font.family'] = 'Times New Roman'
plt.rcParams['mathtext.fontset'] = 'stix'  # 使数学文本也使用相似字体

# 设置全局字体大小
plt.rcParams.update({'font.size': 14})  # 默认字体大小
plt.rcParams.update({'axes.labelsize': 16})  # 坐标轴标签
plt.rcParams.update({'axes.titlesize': 16})  # 标题
plt.rcParams.update({'xtick.labelsize': 14})  # x轴刻度标签
plt.rcParams.update({'ytick.labelsize': 14})  # y轴刻度标签
plt.rcParams.update({'legend.fontsize': 14})  # 图例

keys = [["Hammer Fail"], ["Tactic Execution"], ["Syntax Error - Term Lang"],
        ["Syntax Error - Undefined Fact"], ["Exceeds Window", "Unknown"], ["Syntax Error - Proof Lang"]]
def get_key(key, set):
    ret = 0
    for k in key:
        ret += set[k]
    return ret
values_minilang = [get_key(key, minilang_count) / minilang_case_num * 100 for key in keys]
values_isar = [get_key(key, isar_count) / isar_case_num * 100 for key in keys]
texts = ["Hammer Fails", "Operation Fails", "Term Lang", "Undefined Lemma", "Other", "Proof Lang"]

y = np.arange(len(keys))
trunc_high = 16.0  # 截断值
trunc_low = 5.0

# 计算拆分后的低区间与高区间数据
values_minilang_low = [min(v, trunc_low) for v in values_minilang]
values_isar_low = [min(v, trunc_low) for v in values_isar]
values_minilang_high = [v - trunc_high if i == 0 else 0 for i, v in enumerate(values_minilang)]
values_isar_high = [v - trunc_high if i == 0 else 0 for i, v in enumerate(values_isar)]
max_high = max(values_minilang_high + values_isar_high)

# 创建带断轴的图：左右两个子图共用 y 轴
fig, (ax_low, ax_high) = plt.subplots(
    1, 2,
    sharey=True,
    gridspec_kw={'width_ratios': [1, 1]},
    figsize=(10, 6)
)

fig.subplots_adjust(wspace=0.1)

# 定义两种颜色
color_minilang = '#F2EAAC'
color_isar = '#ACEAF2'

# 定义错开的偏移量
offset = 0.2

# 低区间子图：错开两组数据
for i in range(len(keys)):
    # MiniLang 在上方显示
    ax_low.barh(y[i] + offset, values_minilang_low[i], height=0.4, color=color_minilang, 
                label='MiniLang' if i == 0 else "")
    # Isar 在下方显示
    ax_low.barh(y[i] - offset, values_isar_low[i], height=0.4, color=color_isar, 
                label='Isar' if i == 0 else "")

ax_low.set_xlim(0, trunc_low)
ax_low.spines['right'].set_visible(False)
ax_low.tick_params(right=False)  # 增大刻度标签字体
#ax_low.set_yticks(y)
ax_low.set_yticklabels(texts)  # 使用短文本并增大字体

# 设置 X 轴刻度标签带有百分号
ax_low.set_xticks([0, 1, 2, 3, 4, 5])
ax_low.set_xticklabels(['0%', '1%', '2%', '3%', '4%', '5%'])

# 在 A 类条形末端添加省略号
ax_low.text(trunc_low + 0.35, y[0], '...', va='center', ha='right')  # 增大省略号字体

# 高区间子图：仅显示 A 的截断后部分 (450–max)，同样错开显示
for i in range(len(values_minilang_high)):
    # MiniLang 在上方显示
    ax_high.barh(y[i] + offset, values_minilang_high[i], height=0.4, left=trunc_high, 
                 color=color_minilang)
    # Isar 在下方显示
    ax_high.barh(y[i] - offset, values_isar_high[i], height=0.4, left=trunc_high, 
                 color=color_isar)

ax_high.set_xlim(trunc_high, 21)
ax_high.spines['left'].set_visible(False)
ax_high.tick_params(left=False)  # 增大刻度标签字体
ax_high.set_yticks(y)
ax_high.set_yticklabels([])

# 设置 X 轴刻度标签带有百分号
x_ticks_high = np.arange(trunc_high, trunc_high + max_high + 5, 5)
ax_high.set_xticks(x_ticks_high)
ax_high.set_xticks([16,17,18,19,20])
ax_high.set_xticklabels(['16%','17%','18%','','20% PISA cases'])

# 绘制断轴"锯齿"标记
d = .008
# 计算60度角的y变化量 (tan(60°) ≈ 1.732)
dy = d * 1.732  # 60度角的y变化量

for ax in (ax_low, ax_high):
    kwargs = dict(color='k', clip_on=False, linewidth=1.2)  # 增加线宽使标记更明显
    if ax is ax_low:
        # 左侧子图右边缘的标记，约60度角
        ax.plot((1 - d, 1 + d), (-dy, +dy), transform=ax.transAxes, **kwargs)
        ax.plot((1 - d, 1 + d), (1 - dy, 1 + dy), transform=ax.transAxes, **kwargs)
    else:
        # 右侧子图左边缘的标记，约60度角
        ax.plot((-d, +d), (-dy, +dy), transform=ax.transAxes, **kwargs)
        ax.plot((-d, +d), (1 - dy, 1 + dy), transform=ax.transAxes, **kwargs)

# 添加图例，只在 ax_low 上添加一次
handles, labels = ax_low.get_legend_handles_labels()
by_label = dict(zip(labels, handles))
ax_high.legend(by_label.values(), by_label.keys(), loc='best')  # 增大图例字体

# 在柱子右侧标注数值
for i, text in enumerate(texts):
    # 找出当前类别两个条形中较长的一个
    max_length_low = max(values_minilang_low[i], values_isar_low[i])
    
    # 只有当至少有一个条形存在时才添加标注
    if max_length_low > 0:
        # 标注位置：在最长条形的右侧，垂直居中于两个条形之间
        label_x = max_length_low + 5  # 向右偏移5个单位
        label_y = y[i]  # 垂直居中
        label_text = f"{text} (M={values_minilang[i]:.1f}%, I={values_isar[i]:.1f}%)"
        if i in [4,5]:
            ax_high.text(13, label_y, label_text, va='center', ha='left')
        elif values_minilang[i] >= 15.0:
            ax_low.text(0.2, label_y, label_text, va='center', ha='left')
        else:
            ax_high.text(trunc_high, label_y, label_text, va='center', ha='left')

## 对于高区间，特殊处理：标注放在条形内部
#if values_minilang_high[0] > 0 or values_isar_high[0] > 0:
#    max_length_high = max(values_minilang_high[0], values_isar_high[0])
#    # 计算中心位置，将标签放在条形内部而不是右侧
#    label_x = trunc_high + max_length_high / 2
#    label_y = y[0]
#    label_text = f"MiniLang: {values_minilang[0]}, Isar: {values_isar[0]}"
#    
#    # 确保标签内容适合条形宽度
#    # 如果条形较宽，使用完整标签
#    if max_length_high > 200:  # 阈值可以根据实际情况调整
#        ax_high.text(label_x, label_y, label_text, 
#                    va='center', ha='center', fontsize=10, fontweight='bold')
#    else:
#        # 如果条形较窄，只显示数值
#        compact_text = f"M:{values_minilang[0]}\nI:{values_isar[0]}"
#        ax_high.text(label_x, label_y, compact_text, 
#                    va='center', ha='center', fontsize=9, fontweight='bold')

# 移除 tight_layout，它会覆盖我们的间距设置
# plt.tight_layout()
plt.subplots_adjust(left=0.02, right=0.99, top=0.975, bottom=0.12)  # 手动调整边距
plt.show()
