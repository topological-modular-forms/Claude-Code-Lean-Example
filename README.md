# Making Claude Code Prove the Irrationality of the Square Root of 2.
This is a small demonstration for how Claude Code may be used to formalise proofs using Lean.

For this, we’ll be tasking it with proving the irrationality of $\sqrt{2}$:
<img width="2998" height="872" alt="image" src="https://github.com/user-attachments/assets/a42fe5a0-3dc4-488f-813a-8c7593317293" />
(The fancy rainbow-coloured `ultrathink` keyword allocates maximum compute budget to it, so it “thinks” for longer. This is useful for initial requests, where proper planning could make the difference between a failed project and a successful one.)

Claude Code can ask you questions to better understand your goals:

<img width="48%" alt="image" src="https://github.com/user-attachments/assets/3a0a053a-523c-454d-bfe9-fc791a0de327" />
<img width="48%" alt="image" src="https://github.com/user-attachments/assets/d2a78524-85a9-4f5d-ba72-c27d3da127cd" />

It can also make TODO lists with tasks it has to accomplish, plan, etc., as well as run commands:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/c18ea9f8-6983-45a7-840d-39ef4ece1348" />

It can write files by itself, as well as create them if they don’t exist:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/fc0d03fb-4642-4ad7-8ff7-c0c56221f77d" />

It can also identify flaws in its work and self-correct:

<img width="70%" alt="image" src="https://github.com/user-attachments/assets/2b4d838f-fce1-47fc-bef1-597fed99b83d" />

It will try to compile the code, debug it if it doesn’t compile, and keep working until it eventually does:

<img width="70%" height="1354" alt="image" src="https://github.com/user-attachments/assets/8ed436b4-116e-4848-a909-17437ced72be" />

After several iterations, Claude Code has produced a compilable proof:

It even supports tools allowing you to improve the proofs:

