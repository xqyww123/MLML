import evaluation.failure_analysis as fa
import os
import json
import matplotlib.font_manager as fm

if os.path.exists("tasks/Baldur/minilang_errors.json"):
    (minilang_total, minilang_count, minilang_case_num) = json.load(open("tasks/Baldur/minilang_errors.json"))
else:
    minilang_count = {}
    minilang_total1, minilang_case_num1 = fa.analyze_failure(
        "tasks/Baldur/results/minilang_DPSK_pass8_result.db",
        "tasks/Baldur/results/responses-deepseek-prover-minilang-pass1.jsonl",
        "reasonwang/deepseek-prover-minilang",
        4020,
        minilang_count
    )

    minilang_total2, minilang_case_num2 = fa.analyze_failure(
        "tasks/Baldur/results/minilang_Llemma_pass1_result.db",
        "tasks/Baldur/results/responses-llemma-minilang-pass1.jsonl",
        "EleutherAI/llemma_7b",
        4020,
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
        #"tasks/Baldur/results/responses-deepseek-prover-isar-raw-SH-eval_data_isar-raw-SH.db",
        #"tasks/Baldur/results/responses-deepseek-prover-isar-raw-SH-eval_data_isar-raw-SH.jsonl",
        "tasks/Baldur/results/isar-SH_DPSK_pass1_result.db",
        "tasks/Baldur/results/responses-deepseek-prover-isar-SH-pass1.jsonl",
        "reasonwang/deepseek-prover-isar",
        4020,
        isar_count
    )

    isar_total2, isar_case_num2 = fa.analyze_failure(
        #"tasks/Baldur/results/responses-llemma-isar-raw-SH-eval_data_isar-raw-SH.db",
        #"tasks/Baldur/results/responses-llemma-isar-raw-SH-eval_data_isar-raw-SH.jsonl",
        "tasks/Baldur/results/isar-SH_Llemma_pass1_result.db",
        "tasks/Baldur/results/responses-llemma-isar-SH-pass1.jsonl",
        "EleutherAI/llemma_7b",
        4020,
        isar_count
    )
    isar_total = isar_total1 + isar_total2
    isar_case_num = isar_case_num1 + isar_case_num2
    print(isar_total)
    with open("tasks/Baldur/isar_errors.json", "w") as f:
        json.dump((isar_total, isar_count, isar_case_num), f)

# if os.path.exists("tasks/Baldur/minilang_errors-no-SH.json"):
#     (minilang_total, minilang_count, minilang_case_num) = json.load(open("tasks/Baldur/minilang_errors-no-SH.json"))
# else:
#     minilang_count = {}
#     minilang_total1, minilang_case_num1 = fa.analyze_failure(
#         "tasks/Baldur/results/minilang-DS-no-SH_pisa_result.db",
#         "tasks/Baldur/results/minilang-DS_response.jsonl",
#         "reasonwang/deepseek-prover-minilang",
#         4022,
#         minilang_count
#     )
# 
#     minilang_total2, minilang_case_num2 = fa.analyze_failure(
#         "tasks/Baldur/results/minilang-no-SH_pisa_result.db",
#         "tasks/Baldur/results/minilang-no-SH_response.jsonl",
#         "EleutherAI/llemma_7b",
#         4022,
#         minilang_count
#     )
# 
#     minilang_total = minilang_total1 + minilang_total2
#     minilang_case_num = minilang_case_num1 + minilang_case_num2
#     print(minilang_total)
#     with open("tasks/Baldur/minilang_errors.json", "w") as f:
#         json.dump((minilang_total, minilang_count, minilang_case_num), f)
# 
# if os.path.exists("tasks/Baldur/isar_errors-no-SH.json"):
#     (isar_total, isar_count, isar_case_num) = json.load(open("tasks/Baldur/isar_errors-no-SH.json"))
# else:
#     isar_count = {}
#     isar_total1, isar_case_num1 = fa.analyze_failure(
#         "tasks/Baldur/results/isar-DS_pisa_result.db",
#         "tasks/Baldur/results/isar-DS_response.jsonl",
#         "reasonwang/deepseek-prover-isar",
#         4020,
#         isar_count
#     )
# 
#     isar_total2, isar_case_num2 = fa.analyze_failure(
#         "tasks/Baldur/results/isar_pisa_result.db",
#         "tasks/Baldur/results/isar_response.jsonl",
#         "EleutherAI/llemma_7b",
#         4020,
#         isar_count
#     )
#     isar_total = isar_total1 + isar_total2
#     isar_case_num = isar_case_num1 + isar_case_num2
#     print(isar_total)
#     with open("tasks/Baldur/isar_errors-no-SH.json", "w") as f:
#         json.dump((isar_total, isar_count, isar_case_num), f)

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
plt.rcParams.update({'legend.fontsize': 16})  # 图例

keys = [["Hammer Fail"], ["Tactic Execution"], ["Syntax Error - Term Lang"],
        ["Syntax Error - Undefined Fact"], ["Syntax Error - Proof Lang"], ["Exceeds Window"], ["Unknown"]]
def get_key(key, set):
    ret = 0
    for k in key:
        try:
            ret += set[k]
        except KeyError:
            pass
    return ret
values_minilang = [get_key(key, minilang_count) / minilang_case_num * 100 for key in keys]
values_isar = [get_key(key, isar_count) / isar_case_num * 100 for key in keys]
texts = ["Hammer Fails", "Operation Fails", "Term Lang", "Undefined Lemma", "Proof Lang", "Window Overflow", "Unknown"]

y = np.arange(len(keys))[::-1]  # 倒序排列
trunc_high = 15.5  # 截断值
trunc_low = 6.7

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
    figsize=(10, 2.4)
)

fig.subplots_adjust(wspace=0.3)

# 定义两种颜色
color_minilang = '#230B52'
color_isar = '#E6FFFF'

# 定义错开的偏移量
offset = 0.2

# 低区间子图：创建哑铃图
for i in range(len(keys)):
    # 如果这一行的数据应该只在高区间显示，则跳过
    if values_minilang_high[i] > 0 or values_isar_high[i] > 0:
        continue
        
    # 连接线 - 从小值到大值
    x_start = min(values_minilang_low[i], values_isar_low[i])
    x_end = max(values_minilang_low[i], values_isar_low[i])
    ax_low.plot([x_start, x_end], [y[i], y[i]], 'k-', linewidth=2, alpha=0.7)
    
    # MiniLang 数据点
    ax_low.scatter(values_minilang_low[i], y[i], s=120, color=color_minilang, 
                   edgecolors='black', linewidth=1.5, label='Minilang' if i == 0 else "", zorder=5)
    # Isar 数据点
    ax_low.scatter(values_isar_low[i], y[i], s=120, color=color_isar, 
                   edgecolors='black', linewidth=1.5, label='Thor-style Isar + SH' if i == 0 else "", zorder=5)

ax_low.set_xlim(0, trunc_low)
ax_low.spines['right'].set_visible(False)
ax_low.tick_params(right=False)  # 增大刻度标签字体
#ax_low.set_yticks(y)
ax_low.set_yticklabels(texts)  # 使用短文本并增大字体

# 设置 X 轴刻度标签带有百分号
ax_low.set_xticks([0, 1, 2, 3, 4, 5, 6])
ax_low.set_xticklabels(['0%', '1%', '2%', '3%', '4%', '5%', '6%'])

# 在 A 类条形末端添加省略号
#ax_low.text(trunc_low + 0.35, y[0], '...', va='center', ha='right')  # 增大省略号字体

# 高区间子图：创建哑铃图的高值部分
for i in range(len(values_minilang_high)):
    if values_minilang_high[i] > 0 or values_isar_high[i] > 0:
        # 计算实际值（加回截断值）
        actual_minilang = values_minilang_high[i] + trunc_high if values_minilang_high[i] > 0 else values_minilang[i]
        actual_isar = values_isar_high[i] + trunc_high if values_isar_high[i] > 0 else values_isar[i]
        
        # 连接线
        x_start = min(actual_minilang, actual_isar)
        x_end = max(actual_minilang, actual_isar)
        ax_high.plot([x_start, x_end], [y[i], y[i]], 'k-', linewidth=2, alpha=0.7)
        
        # 数据点
        ax_high.scatter(actual_minilang, y[i], s=120, color=color_minilang, 
                       edgecolors='black', linewidth=1.5, label='Minilang' if i == 0 else "", zorder=5)
        ax_high.scatter(actual_isar, y[i], s=120, color=color_isar, 
                       edgecolors='black', linewidth=1.5, label='Thor-style Isar + SH*' if i == 0 else "", zorder=5)

ax_high.set_xlim(trunc_high, 21)
ax_high.set_ylim(-0.35, len(keys) - 0.55)  # 为顶部留出间距
ax_low.set_ylim(-0.35, len(keys) - 0.55)  # 与右侧子图保持一致的间距
ax_high.spines['left'].set_visible(False)
ax_high.tick_params(left=False)  # 增大刻度标签字体
ax_high.set_yticks(y)
ax_high.set_yticklabels([])

# 设置 X 轴刻度标签带有百分号
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

# 添加图例，从两个子图收集所有标签
handles_low, labels_low = ax_low.get_legend_handles_labels()
handles_high, labels_high = ax_high.get_legend_handles_labels()
all_handles = handles_low + handles_high
all_labels = labels_low + labels_high
by_label = dict(zip(all_labels, all_handles))
ax_high.legend(by_label.values(), by_label.keys(), loc='lower right', edgecolor='none')  # 图例放在右下角

# 在y轴左侧标注数值
for i, text in enumerate(texts):
    label_y = y[i]
    label_text = f"{text} (M={values_minilang[i]:.1f}%, I={values_isar[i]:.1f}%)"
    # 在左侧子图的y轴左侧放置标签，右对齐
    ax_low.text(-0.2, label_y, label_text, va='center', ha='right', transform=ax_low.transData)

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
plt.subplots_adjust(left=0.317, right=0.99, top=0.975, bottom=0.12, wspace=0.15)  # 为左侧标签留出空间并增加子图间距
plt.show()
