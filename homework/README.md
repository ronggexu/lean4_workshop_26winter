# Lean4 Workshop 26Winter 作业提交指南

## 作业格式要求

### 作业1
- **格式**：Markdown (.md)
- **参考案例**：`example.md`
- **提交方式**：按小组提交
- **文件命名**：`hw1_group_{group_id}.md`
  - 例如：`hw1_group_1.md`, `hw1_group_2.md` 等

## GitHub 提交方法（Pull Request）

### 基本操作流程

1. **Fork 仓库**
   - 访问主仓库页面：https://github.com/ronggexu/lean4_workshop_26winter.git
   - 点击右上角的 "Fork" 按钮
   - 选择你的 GitHub 账户作为 fork 目标

2. **克隆到本地**
   ```bash
   git clone https://github.com/[你的用户名]/lean4_workshop_26winter.git
   cd lean4_workshop_26winter
   ```
3. **添加上游仓库**
    ```bash
    git remote add upstream https://github.com/ronggexu/lean4_workshop_26winter.git
    ```
4. **创建分支**
    ```
    # 以组1为例
    git checkout -b group_1
    ```
5. **编辑作业文件**
   在 `homework/hw1` 目录下创建或编辑你的作业文件, 例如：`hw1_group_1.md`
6. **提交更改**
    ```bash
    git status      # 查看文件更改状态
    git add .       # 添加所有更改
    git status      # 再次查看文件添加无误
    git commit -m "Add homework 1 for group 1"
    git push origin group_1
    ```
7. **创建 Pull Request**
   - 访问你的 GitHub fork 页面
   - 点击 "Compare & pull request"
   - 填写 PR 标题和描述
   - 确认目标分支正确（主仓库的 main 分支）
   - 点击 "Create pull request"

**注意事项**

在创建 PR 前，建议先同步上游仓库的最新更改:
```bash
git fetch upstream
git merge upstream/main
```