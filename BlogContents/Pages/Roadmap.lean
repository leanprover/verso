import LeanDoc

open LeanDoc.Genre (Blog)

set_option pp.rawOnError true

#doc (Blog) "The Lean FRO Roadmap" =>


# Vision

The [Lean Focused Research Organization (FRO)](https://lean-fro.org) envisions a future where [Lean](https://lean-lang.org), a proof assistant and programming language, becomes a pivotal tool in driving innovation and progress across diverse fields. Our vision extends to formal mathematics, software and hardware verification, software development, AI research for mathematics and code synthesis, as well as new methodologies in math and computer science education. We are dedicated to fostering a dynamic, decentralized ecosystem, thriving on diversity and collaboration. This includes engaging with a global community, encouraging open-source contributions, and forging educational partnerships, thereby ensuring that our efforts resonate widely. Our aim is to make Lean an indispensable resource not only for researchers and developers but also for educators and students.


# Mission

Our mission focuses on enhancing the Lean system in key areas: scalability, usability, documentation, and proof automation, while also broadening its application in various fields such as education, research, and industry. Over the next five years, we are dedicated to advancing Lean's capabilities and expanding its influence, ensuring it becomes an indispensable tool in these diverse domains. A pivotal aspect of our mission is to steer Lean towards self-sustainability, laying a strong foundation for its enduring growth and widespread utilization.



* **Scalability Enhancements**: Our goal is to optimize Lean for handling increasingly complex and large-scale projects, such as Mathlib, ensuring it meets the demands of advanced computational and analytical tasks in various domains.
* **Usability Improvements**: We aim to make Lean more intuitive and user-friendly, enhancing its interface and functionality to cater to a wide range of users, from mathematicians and software developers to verification engineers, AI researchers, and the academic community.
* **Advancements in Proof Automation**: We aim to decrease the formalization overhead and make it easier to write verified programs and mathematical proofs by improving automation.
* **Documentation and Documentation Generation Tools**: Committing to high-quality, accessible documentation, we will develop and provide advanced documentation authoring tools alongside traditional resources. This will facilitate the creation of user's guides, tutorials, best practices, and detailed technical documentation. Our aim is to ensure that these resources are not only thorough and clear but also continuously updated and easy to navigate for all users, from beginners to advanced practitioners in various disciplines.
* **Broad Application in Diverse Fields**: We are dedicated to demonstrating Lean's utility and adaptability in a variety of sectors. Our focus extends equally to formal mathematics, software and hardware verification, AI research for mathematics and code synthesis, as well as innovative methodologies in math and computer science education. By showcasing Lean's versatility, we aim to establish it as a valuable tool in each of these domains, and we believe that tools developed in one domain will improve the experience of users working in other domains.
* **Building a Diverse and Inclusive Community**: We are committed to fostering a dynamic, inclusive community around Lean. This involves engaging with stakeholders from academia, industry, and educational sectors to create a decentralized network of collaboration and innovation.
* **AI Research and Verified Code Synthesis**: We aspire for Lean to become  an indispensable tool in AI research, particularly in the realms of mathematics and verified code synthesis. Lean is an ideal target language for generative AI. Lean’s expressive logic provides a unique training environment for logic and reasoning. Lean enables trustworthy AI-driven code synthesis by allowing models to generate both code and proofs of specifications.
* **Steering Towards Self-Sustainability**: A critical aspect of our mission is to establish a sustainable operational and financial model for Lean. This will involve developing strategies for long-term funding, community support, and organizational growth, laying the groundwork for future independence and self-sufficiency.

Furthermore, we aim to transition to a foundation model, similar to those of the Rust and Linux Foundations. This transition will mark a significant step in establishing Lean as a widely supported tool, laying the groundwork for its continuous growth and evolution.


# Tracking Progress

To effectively gauge the adoption and impact of Lean, the Lean FRO monitors the following key metrics:



* **Number of Monthly Active Users**: This metric is tracked using data from GitHub, the [Lean Zulip chat](https://leanprover.zulipchat.com/stats), and the Lean website. Regular monitoring of user engagement across these platforms will provide insights into the growing user base and community activity.
* **Number of Courses Using Lean**: This information is tracked by Patrick Massot and Rob Lewis on the [Lean Community website](https://leanprover-community.github.io/teaching/courses.html). The number of educational courses incorporating Lean will be a vital indicator of its acceptance and effectiveness in academic settings.
* **Number of Packages**: Currently tracked using [GitHub labels](https://github.com/topics/lean4), we aim to transition to using Reservoir, a Lean-focused package registry akin to crates.io and CTAN, for a more streamlined and comprehensive tracking process.
* **Overhead Factor**: The Overhead Factor of a proof is the ratio (proof length in Lean)/(proof length in prose). It is currently often greater than 20, with users having to manually provide details for trivial proof steps. This metric, which varies significantly based on the topic and complexity of mathematics being formalized in Lean, is crucial for both technical and user experience improvements. We are developing methods to reliably measure the Overhead Factor, recognizing its importance as a technical challenge and a UX deliverable.
* **Build Time**: The time required to compile and check one million lines of Lean code is a key measure of the system’s efficiency. Our goal is to reduce this build time, enhancing both technical performance and user experience. This metric is currently tracked at [speed.lean-lang.org](http://speed.lean-lang.org).


# A Laser-Focused First Year

At the Lean FRO, we recognize that there are several obstacles to the wider adoption of Lean that, while significant, are small enough to be removed by our team. Addressing these challenges is our foremost priority in the first year of the Lean Focused Research Organization (FRO).



* **Taking care of "paper cuts":** We will be vigilant in identifying small yet painful issues that occur when using Lean, such as insufficient or misleading error messages, unexpected performance issues, or needlessly brittle tooling.
* **Eliminating Obstacles and Enhancing User Experience**: We will refine the user interface, streamline processes, and eliminate bugs or inconveniences that hinder the user experience.
* **Improving Documentation**: We are investing in improving and expanding Lean's documentation. This includes creating comprehensive, easy-to-understand guides and resources that cater to users at all levels – from beginners to advanced practitioners.
* **Developing Cloud Build Support**: A major technical endeavor for us will be the development of robust cloud build support for Lean packages. That is, allowing users to quickly download prebuilt artifacts rather than perform a slow build from the source. This initiative will facilitate more efficient and scalable usage of Lean, particularly in handling large and complex projects,
* **Reservoir, the Lean Package Registry**: We will launch Reservoir, the Lean package repository. It will serve not just as a registry for packages, but also as a platform to report package incompatibilities and breakages. Reservoir will be instrumental in providing cloud build support for all registered packages, fostering a rich package ecosystem.
* **Standard Library**: We envision a standard library akin to Rust’s, but with specifications, proofs and tactics for its main components. The Lean standard library will also serve as the bedrock for many other packages and projects.
* **Enhancing Proof Automation**: Advancing Lean’s proof automation capabilities is another key focus. We aim to make the process of developing and verifying proofs more efficient and user-friendly.
* **Tooling for Decentralized Work and a Rich Package Ecosystem**: We plan to provide tools that enable users to work in a decentralized manner. This includes refactoring tools to eliminate unnecessary dependencies and assist in breaking mono-repositories into smaller, more manageable units. Such tools are essential for cultivating a rich and diverse package ecosystem.

In focusing on these areas, we aim to make significant strides in enhancing the appeal and functionality of Lean. By the end of the first year, we anticipate a marked improvement in user experience, a more robust support infrastructure, and a strong foundation for the diverse and thriving community we aspire to build.


# Deliverables

As we chart our course for the next five years, the Lean Focused Research Organization (FRO) is committed to developing and enhancing a series of key components integral to the Lean ecosystem. This section outlines these deliverables, detailing the scope and nature of each.


## Preamble: Involvement of External Contributors

We warmly welcome external contributors to participate in this exciting journey of growing and improving Lean. It's important to note that while there are numerous opportunities for contributors at various levels of expertise, certain critical components require a deep understanding of Lean and a strong track record of reliability, and our core team has to carefully prioritize the use of scarce time on contributor mentorship vs direct technical work. Therefore, **we encourage new contributors to start with less critical components**, which are excellent entry points to get acquainted with Lean's development process and build both technical knowledge and trust with the Lean FRO development team. As contributors gain experience and demonstrate their skills, there will be opportunities to engage with more complex and critical parts of the Lean system.


## 1. Better Error Messages and Diagnostic Tools

**Description**: One of the most time-consuming aspects for users is understanding why something did not work as expected. Exceptional error messages and diagnostic tools are fundamental to enhancing the user experience in any programming language. Drawing inspiration from the Rust community, where the development of superior error messages has been cited as a key factor in its success, we aim to significantly improve the usability of Lean by investing in this area. Developing more intuitive and informative error messages, along with robust diagnostic tools, will make Lean more user-friendly and reduce troubleshooting time for users.

**Role of the Community**: Lean, being developed in Lean itself, offers an excellent opportunity for the community to contribute to this improvement, much like the Rust community's involvement in enhancing their error messages and diagnostic tools. Community contributions will be vital in identifying areas of improvement, suggesting better error messages, and developing tools to diagnose issues more effectively.

**Suitability for Contributors**: This component is open to contributors of all levels. Newcomers to the Lean community can start by identifying common errors and suggesting improvements, while more experienced contributors can work on developing sophisticated diagnostic tools. However, contributors interested in taking a leading role in coordination or documentation should have some prior experience with Lean or similar projects to ensure effective leadership in these areas.


## 2. Test Framework and Benchmarks

**Description**: For both the FRO and end users, tests and benchmarks are essential for maintaining the quality and reliability of Lean code. When robust, they enable the thorough evaluation of the impact of changes to ensure that enhancements do not inadvertently introduce errors or degrade performance. In particular, core tests help outline concrete expectations on the behavior of key components and downstream user tests integrated with Lake and Reservoir can provide a ecosystem-wide picture of toolchain compatibility and enable the rigorous analysis of experimental new features

**Goals and Impact**: Our aim is to define the fundamentals of a new Lean testing framework within the Lean core (and Lake) that can be extended and expanded upon by downstream Lean libraries. We will develop this framework while improving the core test and benchmark suite, expanding and improving both to cover a wider range of scenarios and use cases. With this, the core will eventually serve as a great example of how to do testing in Lean.

**Project Leadership**: Mac Malone is currently responsible for developing the design of the new framework and its integration with Lake, and is consulting with those both inside and outside the FRO on the shape it should take. The transition from theory to practice is still a ways away, with a major component of the current focus being on polishing the existing core test suite to better understand needed features.

**Suitability for Contributors**: This component is suitable for contributors with experience in software development, testing, and benchmarking, as well as those with a deep understanding of Lean's functionalities. New contributors can help by identifying missing use cases and performance bottlenecks, ensuring that the core suite has adequate coverage of the kinds of issues the framework will be expected to be able to test.


## 3. Standard Library

**Description**: The ambition for the Lean Standard Library is to develop a library as comprehensive as Rust's standard library, with the added value of including proofs. This library aims to be a foundational element of the Lean ecosystem, providing users with a robust, extensive collection of well-documented and proven modules and functions.

**Project Leadership**: Joe Hendrix is leading this significant project. His expertise and guidance are pivotal in shaping the library to meet high standards of quality, usability, and comprehensiveness. Scott Morrison is responsible for moving general purpose components from Mathlib to the standard library.

**Guidelines and Scope**: Joe will be providing detailed guidelines for contributing to the Standard Library, outlining its scope and the standards expected from contributions. These guidelines will ensure consistency and quality in the library's development and will be instrumental in guiding community contributors.

**Community Involvement**: The Lean Standard Library is an excellent opportunity for community contributions. Its wide scope and the need for a diverse range of proofs and modules mean that contributors at various levels of expertise can find areas where they can make meaningful additions.

**Suitability for Contributors**: This component is highly suitable for contributors interested in software development and verification. Whether you are a seasoned expert or a newcomer eager to learn and contribute, there are numerous opportunities to engage with the Lean Standard Library project. Contributors are encouraged to collaborate closely with Joe and follow the established guidelines to ensure their contributions align with the library's goals and standards.


## 4. Improved Elaboration

**Description**: The elaborator is a critical component in Lean, responsible for converting Lean notation into kernel terms. This process is fundamental to the way Lean handles formal mathematics and software/hardware verification proofs. However, since there is no definitive specification for the language used in these proofs, we are constantly learning and evolving with the community. Our goal is to enhance the elaborator's usability and address the 'paper cuts'. This ongoing process of refinement is vital to making Lean more intuitive and effective for users.

**Community Feedback and Involvement**: The Lean community plays a pivotal role in this endeavor. Continuous feedback from users about what aspects are working well and which aren’t is invaluable. This information guides our efforts in improving the elaborator. However, due to the complexity and central importance of this component, modifying it requires a deep understanding of Lean's core functionalities.

**Suitability for Contributors**: Given its complexity and fundamental role in Lean, work on the elaborator is not suitable for newcomers to the Lean development community. This component requires advanced knowledge of Lean’s inner workings and is best suited for experienced contributors who have a strong background in the system’s architecture and have built a track record of reliability and expertise within the Lean community.


## 5. Elaboration Efficiency

**Description**: Elaboration is not only a complex but also time intensive process in languages like Lean. Beyond optimizing the implementation of specific steps, there are general improvements we can apply to decrease latency of working with complex Lean code: avoiding redundant work, reporting finished work earlier, and parallelizing work.

**Incremental tactics**: The use of tactics for interactive proof construction is a fundamental aspect of working with Lean. A more incremental execution of tactic steps would enhance the efficiency and responsiveness of this process. By ensuring that tactic results are computed and displayed as quickly as possible independent of the length of the remaining proof or of the preceding unchanged proof, we aim to significantly boost user productivity. This enhancement will not only streamline the proof development process but also eliminate the need for many of the current workarounds.

**Elaboration Parallelism**: This advancement aims to enable different parts of a Lean file to be processed in parallel, thereby significantly improving the system's responsiveness. By parallelizing the elaboration process, we expect to see a noticeable increase in efficiency, especially in handling large and complex files.

**Project Planning and Execution**: This project will involve careful planning and execution to identify the optimal parts of the elaboration process that can be optimized without compromising the correctness and stability of the system.

**Suitability for Contributors**: Due to the technical complexity of this task, this component is not a good match for external contributors.


## 6. VS Code Plugin for Lean

**Description**: The Visual Studio Code (VS Code) plugin for Lean is an essential tool for many Lean users, providing a user-friendly interface and powerful features that enhance the Lean programming experience. Recognizing its importance, the Lean Focused Research Organization (FRO) has appointed Marc Huisinga as the official maintainer and developer of this plugin.

**Current Focus and Development Goals**: Marc's role involves addressing a range of tasks to improve the plugin significantly. This includes fixing various bugs and 'paper cuts' that currently affect user experience, adding missing features that users have requested or that are seen as essential for a more seamless experience, and generally enhancing the overall usability of the plugin.

**Suitability for Contributors**: This component is suitable for contributors with experience in software development, particularly those familiar with Visual Studio Code extension APIs and TypeScript or JavaScript.


## 7. LSP Server

**Description**: The Lean Language Server Protocol (LSP) server is a critical component for Lean users, particularly those using editors like Visual Studio Code. LSP, developed by the Microsoft VS Code team and implemented by various editors, facilitates efficient communication between Lean and the editor, enhancing the overall user experience.

**Development and Maintenance**: Marc Huisinga is at the helm of maintaining and developing the LSP server for Lean. His work is central to ensuring that the LSP server remains reliable, feature-rich, and aligned with the evolving needs of the Lean community.

**Current Focus and New Features**: Marc's current development efforts encompass a range of new features, including auto-completion for imports, syntax, constructor fields, and tactics. He is also working on supporting call and type hierarchies, handling rename requests, and suggesting imports. These enhancements aim to streamline the user's coding experience, making it more intuitive and efficient.

**Improvements in Existing Features**: In addition to new features, Marc is actively involved in fixing and refining existing functionalities, such as 'find-references'. His work ensures that these features remain robust and user-friendly.

**Working on Extensible Design**: A significant aspect of Marc's role involves reworking the LSP server's design to make it more extensible. This new design will allow for easier addition and modification of features in the future, ensuring the LSP server can adapt to the changing needs of Lean users.

**Code Actions**: Marc is also working on adding support for code actions such as: extracting definitions, factoring out variables, proof refactoring, and hole commands, to name a few.

**Community Involvement**: While Marc leads the LSP server development, community feedback is invaluable. Users are encouraged to report issues and suggest improvements.

**Suitability for Contributors**: Given the technical complexity and importance of the LSP server in the Lean ecosystem, this component is most suitable for contributors with advanced knowledge in software development, particularly those experienced with LSP and editor integrations.


## 8. Lake Build System and Package Manager

**Description**: Recognizing the significance of a robust package manager in the success of a programming language, as exemplified by Rust's cargo, Lean has its own equivalent: Lake. Lake serves as Lean's comprehensive build system and package manager, playing a critical role in the Lean ecosystem.

**Development and Maintenance**: Lake is developed and maintained by Mac Malone. His efforts are focused on ensuring that Lake not only meets but exceeds the needs and expectations of the Lean community.

**Current Focus**: Mac's current development priorities for Lake include enhancing performance, integration with Reservoir, resolving 'paper-cuts' or minor yet impactful issues, and addressing problems and needs highlighted by the Lean user community. These improvements are geared towards making Lake more efficient, user-friendly, and reliable. One current major project is built-in support for build artifact caching through Reservoir..

**Community Feedback and Involvement**: The Lean community's input is invaluable in shaping the development of Lake. Feedback from users on their experiences and challenges with Lake guides Mac’s efforts in refining and evolving the system. Community members are encouraged to report issues, suggest enhancements, and potentially contribute to Lake’s development.

**Suitability for Contributors**: This component is suitable for contributors with a background in software development, particularly those with experience or interest in package management systems and build tools. While Mac leads the development, there are opportunities for contributors to assist with various aspects of Lake’s development, especially those willing to understand the specific requirements and nuances of the Lean ecosystem.


## 9. Reservoir Package Registry

**Description**: In addition to serving as a traditional package registry for Lean, Reservoir aims to be a significant leap forward in managing and facilitating package compatibility and development. Its design goes beyond mere storage and distribution of packages, aiming to serve as a comprehensive breakdown of Lean's ecosystem..

**Advanced Features**: Key features of Reservoir include tracking package compatibility, identifying breakages, and storing and distributing package artifacts. These functionalities are designed to streamline the development process, enhance collaboration among Lean users, and ensure a high level of reliability and efficiency in package management.

**Development and Leadership**: Mac Malone is the lead developer of Reservoir.

**Suitability for Contributors**: Given the complexity and pivotal role of Reservoir in the Lean ecosystem, contributors with an understanding of package management systems and advanced skills in web design and software development are best suited for this project.


## 10. Language Extensibility

**Description**: A key goal for Lean is to enhance its extensibility to support complex standalone and embedded languages effectively. This aspect of development focuses on making Lean adaptable and versatile in handling a variety of programming and markup languages, which is essential for its broader applicability and user engagement.

**Inspiration from Racket**: Drawing inspiration from the `#lang` feature in Racket, which allows a source file to indicate that it's written in a separate language with its own syntax, we aim to bring similar functionality to Lean. This feature would allow users to seamlessly integrate and switch between different languages within Lean, enhancing its flexibility and usability for diverse programming needs.

**Improvements to Grammar Authoring Tools**: In theory, Lean parsers can be created to parse arbitrary languages today. In practice, valuable tools for doing so that have been created for implementing the Lean language itself are not sufficiently generic yet to support all language authors, especially around the handling of custom tokens. We aim to support creators of both embedded and standalone languages in Lean better in this regard.

**Project Leadership**: Sebastian Ullrich is leading the development of this crucial component. His expertise and vision are instrumental in guiding the project towards achieving these ambitious goals of language extensibility.

**Suitability for Contributors**: Given the technical complexity and innovative nature of this component, it is best suited for contributors with a strong background in software development.


## 11. Module System

**Description**: The development of a sophisticated Module System for Lean is aimed at enhancing abstraction and minimizing unnecessary recompilation. The introduction of a signature system for Lean modules will be a central feature of this initiative. This system will enable Lean to more effectively determine which parts of a module need recompilation, thereby increasing efficiency and reducing the time spent on redundant computations.

**Impact and Benefits**: By significantly improving abstraction and recompilation avoidance, the Module System will facilitate smoother and faster development workflows. This is especially beneficial for large projects where recompilation of unchanged parts can be time-consuming. The signature system will allow Lean to intelligently and selectively recompile only the necessary parts of the code, thereby optimizing the development cycle.

**Suitability for Contributors**: This component requires contributors with expertise in compiler design, module systems, and a deep understanding of Lean's architecture. It is a technically demanding project, and is not a good match for new contributors.


## 12. Improving Recursion

**Description**: Enhancing the capabilities of Lean in defining recursive functions is a vital component of our development roadmap. We are focused on adding support for mutual structural recursion and partial recursion. A significant part of this effort is also geared towards dramatically improving the heuristics for automatically proving function termination by well-founded recursion.

**Induction Principles**: Another goal in this area is to automate the generation of induction principles for mutually recursive definitions. This will greatly simplify the process of constructing proofs about these definitions, making it more intuitive and efficient for users.

**Enhancing Functionality and Efficiency**: In addition to expanding the kind of recursions we support, we aim to improve the efficiency of these processes and make recursion compilation extensible. This will ensure that the module can adapt and evolve with the growing needs of the Lean community.

**Project Leadership**: This significant effort is led by Joachim Breitner, whose expertise in the field is invaluable. His leadership is pivotal in steering the project towards achieving its ambitious goals.

**Suitability for Contributors**: This task, given its complexity, is most suited for contributors with a strong technical background and a thorough understanding of Lean's programming and proof systems. Contributors under Joachim’s guidance will have the opportunity to delve into both theoretical and practical aspects of recursion in Lean.


## 13. Proof by Reflection Support

**Description**: In the realm of proof automation, the generation of large proof certificates (formal proof objects) checked by the Lean kernel is a common approach. However, these certificates can have a non-trivial size, impacting both scalability and the total size of compiled files. To address this issue, we are focusing on enhancing support for proof by reflection. This technique involves implementing a proof automation procedure and then proving its correctness, which in turn can significantly reduce the size of proof objects.

**Efficient Execution and Kernel Integration**: A practical challenge with proof by reflection lies in the need for efficient execution or interpretation of the proof procedure by the trusted Lean kernel. To facilitate this, we plan to develop a new interpreter that is both efficient and reliable. Given that this interpreter will be a part of the Lean trusted codebase, extreme care and thorough testing are essential to ensure its correctness and security.

**Scope of Development**: The new interpreter is estimated to be around 1,000 lines of code. The development process will emphasize simplicity while maximizing efficiency and reliability.

**Project Leadership**: Joachim Breitner will be leading this project, bringing his expertise to the forefront in this critical development area. His role will be pivotal in guiding the project to success and ensuring the new feature aligns with the needs and expectations of the Lean community.

**Suitability for Contributors:** Given its complexity and the critical nature of the work, this component is not a good match for external contributors.


## 14. Continuous Integration

**Description**: Continuous Integration (CI) is a cornerstone of maintaining the quality and reliability of a complex project like Lean, particularly given its many dependencies. The goal is to create a robust CI system that not only ensures the integrity of Lean itself but also safeguards against any changes that might adversely affect dependent projects like the standard library or Mathlib.

**Enhancements in CI**: Scott Morrison is spearheading efforts to improve our continuous integration framework. A key focus of these improvements is to provide prompt and accurate notifications for Pull Requests (PRs) to the Lean code base that potentially break compatibility with the standard library or Mathlib. This proactive approach in CI will contribute significantly to maintaining the stability and reliability of the Lean ecosystem.

**Future Vision**: Looking ahead, we envision connecting our CI to Reservoir to include checks for other libraries built on Lean. This expansion will provide a comprehensive safety net, ensuring that updates to Lean do not inadvertently disrupt the wider ecosystem of libraries and tools that depend on it.

**Project Leadership**: Under Scott Morrison’s leadership, the project will focus on implementing these enhancements while balancing the needs of rapid development and thorough testing. Scott’s experience and expertise in software development and integration are crucial in guiding this project towards success.

**Suitability for Contributors**: While Scott leads the CI improvement efforts, there are opportunities for contributors with experience in software development, particularly those familiar with CI tools and practices. Contributors can assist in various aspects, from developing new CI scripts to optimizing existing processes.


## 15. Proof Automation

**Description**: Proof automation is a crucial area for Lean, given its profound impact on the efficiency of proof development. Although significant strides have been made in this domain, there remains substantial room for improvement and innovation. The overarching goal is to achieve an overhead factor of less than or equal to 5, which would mark a significant milestone in proof automation efficiency.

**Challenges in Dependent Type Theory**: One of the primary challenges in enhancing proof automation for Lean stems from its foundation in dependent type theory. Techniques that have been effective in first-order logic, such as those used in the Z3 SMT solver, do not easily translate to dependent type theory. This gap necessitates considerable research and development to devise new methods and tools suitable for Lean’s foundational framework.

**Sub-Projects and External Contributions**: The field of proof automation within Lean encompasses numerous sub-projects, each addressing different aspects of this broad area. Notably, many important projects like Aesop are being developed by external contributors, highlighting the collaborative nature of this endeavor.

**Omega for Lean 4**: A specific project of note is the development of omega, a tactic for linear integer arithmetic, for Lean 4 by Scott Morrison. This project signifies a dedicated effort to enhance specific proof automation capabilities within the Lean ecosystem, contributing to the broader goal of making proof development more efficient and user-friendly.

**Project Diversity and Contributor Suitability**: Given the variety of sub-projects under the umbrella of proof automation, there are opportunities for contributors with a wide range of skills and interests.


## 16. Documentation Authoring Tool

**Description**: A key initiative for the Lean community is the development of a comprehensive Documentation Authoring Tool. This tool aims to be a one-stop solution for creating various Lean-related documents, including manuals, tutorials, lecture notes, and blog posts. The objective is to have it fully integrated into the Lean ecosystem, offering a seamless and efficient documentation creation experience.

**Features and Functionalities**: The tool will boast a range of features designed to meet the diverse needs of Lean documentation creators. These include:



* Custom support for various documentation genres, including textbooks, research papers, blog posts, and software manuals
* Tight integration with Lean, with both support for embedded Lean code and extensibility in Lean itself
* High-quality support for multiple output formats, including HTML, EPUB, and LaTeX, depending on genre
* Extensible support for figures, bibliographies, indices, and other structured document components
* Cross-reference support both within and between documents
* Robust support from the Lean language server, including showing the documentation's table of contents in the editor outline view, code actions to relieve repetitive tasks, and all the usual Lean features
* An appealing and user-friendly design to enhance the overall user experience.

**Project Leadership**: David Thrane Christiansen is leading this project, bringing his expertise in both Lean, domain-specific languages, technical writing, and documentation tools to the forefront. His role is crucial in guiding the development of this tool to ensure it meets the community's needs and aligns with Lean's standards.

**Community Involvement and Feedback**: The involvement and feedback from the Lean community are essential in shaping this tool. Users' insights and suggestions will be invaluable in refining the tool's features and functionalities.

**Suitability for Contributors**: This project is suitable for contributors with a background in software development, particularly those with experience or interest in documentation tools, typography, technical writing, UI/UX design, and integration with programming languages. Contributors are encouraged to work closely with David and the community to ensure the tool effectively meets the diverse documentation needs of Lean users.


## 17. Reference Manual

**Description**: A comprehensive reference manual for Lean is an essential yet currently missing piece in the Lean ecosystem. The development of this manual is a significant project aimed at providing a detailed and authoritative resource for Lean users. This manual will serve as a go-to guide for understanding the intricacies of Lean, from its basic syntax and functionalities to advanced features.

**Purpose and Impact**: The availability of a thorough reference manual will greatly aid the community in effectively answering questions on platforms like the Lean Zulip channel. It will contribute to the scalability of the community by providing a reliable source of information, reducing repetitive queries, and enhancing the overall usability of the system. Additionally, the manual will serve as a foundational resource for user-driven manuals and guides, fostering a deeper understanding of Lean.

**Project Leadership**: David Thrane Christiansen is leading the creation of the Lean reference manual. His expertise and deep understanding of Lean make him ideally suited for this task. Under his guidance, the manual will be developed to accurately and comprehensively cover all aspects of Lean.

**Community Involvement**: Collaboration and input from the Lean community are crucial in this endeavor. Contributions from experienced Lean users and feedback from a diverse user base will ensure that the manual is both comprehensive and accessible to users at all levels.

**Suitability for Contributors**: While David Thrane Christiansen leads the project, there are opportunities for contributors who are well-versed in Lean’s functionalities to assist in writing and reviewing sections of the manual. This task is particularly suited for those with a strong grasp of Lean’s features and a passion for education and documentation.


## 18. Machine Learning integration

**Description**: There is widespread interest in integration between Lean and machine learning applications, both to bring machine learning tools to Lean users as assistants, and to use Lean as a gym for machine learning reasoning tasks. Examples of early deployments of Lean specific tools are LeanInfer, LLMStep, Sagredo, and Moogle. The IMO Grand Challenge is an important goal for machine learning mathematical reasoning. A number of companies are actively using Lean in machine learning today. We want to provide common tools for the ML community in the form of 1) easy data extraction tools for the Lean ecosystem, 2) a REPL and gym for interacting with Lean from external systems, 3) a common interface for providing tactic suggestions, auto-formalization, in-editor assistance, and premise selection.

**Project Leadership**: From the FRO, Scott Morrison will take the lead in developing these tools and frameworks, in consultation with external users and ML experts. A REPL already exists that is being used in ML applications, maintained by Scott. Further development of the REPL, and improvements and ecosystem wide deployment of data extraction tools is a priority. Developing a common interface for tactic suggestions, auto-formalization, and premise selection will come after that.

**Suitability for Contributors**: There are many opportunities to contribute here. The FRO hopes to provide coordination, and a baseline of generically useful tools, but training models and providing backends for services will only happen if external users are engaged. These tasks are well-suited to those with machine learning experience. Lean metaprogramming experience is useful, but the FRO can assist in linking up contributors with ML experience and Lean experience.


## 19. Code Formatter

**Description**: The development of a Code Formatter tool is a crucial addition to Lean's suite of tools, particularly for modern integrated development environments. This tool is designed to automatically format Lean code, ensuring that it adheres to consistent coding conventions. By standardizing the style and formatting of code, the tool will contribute to clearer, more readable, and maintainable code bases.

**Importance and Usage**: In the context of Lean package development, a reliable code formatter becomes essential. It enables developers to enforce uniform coding standards across their projects, reducing discrepancies and enhancing collaboration. This tool is especially beneficial in large projects or when multiple contributors are involved, as it ensures a unified coding style.

**Features and Capabilities**: The Code Formatter will offer a range of formatting options and be customizable to suit different coding styles and preferences. Its integration with Lean's development environment will allow for seamless and automated code formatting, either on-demand or as part of the editing process.

**Suitability for Contributors**: This project is suitable for contributors with experience in software development, particularly those familiar with coding standards and formatter tool development. The task requires a good understanding of Lean syntax and coding practices, as well as the ability to implement efficient and reliable formatting algorithms.


## 20. Website

**Description**: The development of a comprehensive website for Lean is a key initiative to centralize and streamline access to Lean-related information. This website aims to serve as a portal to Lean, from beginner tutorials to advanced documentation.

**User-Friendly Design and Content**: A primary focus of the website is to provide step-by-step instructions for new users, guiding them through the basics of Lean and helping them get started effectively. For both new and experienced users, the website will offer extensive documentation, resources, and tools, making it a valuable resource for the entire Lean community.

**Harmonization of Design Across Platforms**: The Lean FRO leadership recognizes the importance of a cohesive and professional design across all Lean-related platforms. Efforts are underway to hire a professional designer to harmonize the aesthetics and user experience across the FRO website, the Lean site, documentation pages, Loogle, Reservoir, and other related platforms. This unified design approach is aimed at creating a consistent and appealing visual identity for Lean.

**Community Involvement and Feedback**: Input from the Lean community will be vital in shaping the website. User feedback will inform the design and content, ensuring that the website meets the needs and preferences of a diverse user base.

**Project Execution and Contributor Suitability**: While a professional designer will lead the visual aspects of the website, there are numerous opportunities for contributors with skills in web development, content creation, and user experience design. Contributors can assist in various aspects such as developing website features, writing content, or providing feedback on design and usability.


## 21. New Code Generator (Starting on Year 2)

**Description**: The development of a new and improved code generator is a significant initiative for Lean. This component is crucial since Lean users often implement theory-specific automation and extensions using Lean itself. Mathlib, as an example, is not just a repository of mathematical theories but also includes proof automation code and extensions written in Lean.

**Goals and Impact**: While Lean 4 already generates efficient code, there is considerable scope for enhancement. The aim is to optimize the code generator to further improve the performance and efficiency of Lean. This is not just about enhancing Lean’s own performance; it extends to optimizing the performance of every user-written extension and proof automation procedure. Thus, improvements in the code generator will directly contribute to the scalability and efficiency of the entire Lean ecosystem.

**Dependence on Other Features**: Several other planned features, such as a Debugger, are dependent on improvements to the code generator. As such, progress in this area will have a cascading positive effect on other components and functionalities within Lean.

**Suitability for Contributors**: This component is suited for contributors with a strong background in compiler design, code optimization, and a deep understanding of Lean's architecture. The task is technically demanding and requires contributors who can navigate the complexities of code generation and optimization. It is not suited to new contributors.


## 22. Debugger (Starting on Year 2 or 3)

**Description**: The introduction of a Debugger for Lean programs addresses a commonly requested feature from the Lean user community. As users increasingly write programs, Lean extensions, and proof automation procedures directly in Lean, the need for a robust debugging tool has become more pronounced. This tool will significantly enhance the development experience within Lean, particularly for complex coding and automation tasks.

**Dependency on Code Generator Improvements**: The development and effectiveness of the Debugger are closely linked to the progress made in the New Code Generator task. Enhancements in code generation, as previously described, will directly impact the capabilities and performance of the Debugger, making it more efficient and user-friendly.

**Benefits for Programming and Usability**: While the Debugger will primarily assist users in identifying and resolving issues in Lean programs and extensions, it also extends benefits to those using Lean as a programming language. By providing insights into the execution of Lean code and facilitating the identification of bugs and inefficiencies, the Debugger will improve the overall usability and efficiency of Lean as a programming and automation tool.

**Suitability for Contributors**: This project is suitable for contributors with experience in developing debugging tools, a strong understanding of software development processes, and familiarity with Lean’s architecture. Given the technical complexity of this task, it is not a good match for new contributors.


## 23. Metaprogramming Guide (Starting on Year 2)

**Description**: The Metaprogramming Guide for Lean is an essential resource for the community, especially for those interested in extending Lean’s capabilities and adding new functionalities. While the community has been actively developing and maintaining this manual, there is a need to further refine and enhance it.

**Enhancement and Completion**: Following the release of a polished Reference Manual, David Thrane Christiansen will undertake the task of ensuring that the Metaprogramming Manual is comprehensive, approachable, and user-friendly. The aim is to make the manual a definitive guide for metaprogramming in Lean, covering all aspects from basic to advanced techniques.

**Empowering Contributors**: A key goal of the Metaprogramming Manual is to empower new contributors. By providing clear, detailed, and accessible information, the manual will enable newcomers to effectively extend Lean and contribute to its ecosystem. This approach aligns with the vision of decentralization, where a broader base of contributors can add value and functionality to Lean.

**Suitability for Contributors**: While David Thrane Christiansen will lead this project, there are opportunities for contributors with experience in Lean metaprogramming to assist in writing, reviewing, and providing feedback on the manual. This task is well-suited for those who are passionate about education, documentation, and the dissemination of knowledge within the Lean community.
