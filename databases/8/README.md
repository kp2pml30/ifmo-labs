1.     Запросы из предыдущих ДЗ

1.S. Students

Хэш-индекс на префикс упорядоченного индекса: create index StudentGroupToId on Students using hash (GroupId); create unique index StudentsGidToSid on Students using btree (GroupId, StudentId);
Хэш-индекс на префикс упорядоченного индекса: create unique index StudentIdAndGroupToRecord on Students using hash (StudentId, GroupId); create unique index StudentsGidToSid on Students using btree (GroupId, StudentId);
Неэффективный или бесполезный индекс: create unique index StudentIdAndGroupToRecord on Students using hash (StudentId, GroupId);
Индекс мало/бесполезен: ДЗ-5.6.1 для create index StudentNameIdx on Students using btree (StudentName);
Индекс мало/бесполезен: ДЗ-5.5.1 для create index StudentGroupToId on Students using hash (GroupId);
Индекс мало/бесполезен: ДЗ-5.5.2 для create index StudentGroupToId on Students using hash (GroupId);
Индекс мало/бесполезен: ДЗ-5.5.3 для create index StudentGroupToId on Students using hash (GroupId);
Индекс мало/бесполезен: ДЗ-6.5.1 для create unique index StudentsGidToSid on Students using btree (GroupId, StudentId);

1.G. Groups

1.C. Courses

Индекс мало/бесполезен: ДЗ-5.5.1 для create unique index CoursesIdUniq on Courses using hash (CourseId);
Индекс мало/бесполезен: ДЗ-5.5.2 для create unique index CoursesIdUniq on Courses using hash (CourseId);
Индекс мало/бесполезен: ДЗ-5.5.3 для create unique index CoursesIdUniq on Courses using hash (CourseId);

1.L. Lecturers

1.P. Plan

Не unique индекс (а должен): create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);
Индекс мало/бесполезен: ДЗ-6.3.2 для create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);
Индекс мало/бесполезен: ДЗ-6.4.1 для create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);
Индекс мало/бесполезен: ДЗ-6.4.2 для create index GiCiExistsInPlan on Plan using hash (GroupId, CourseId);

1.M. Marks

Хэш-индекс на префикс упорядоченного индекса: create index MarkByStudentIdExists on Marks using hash (StudentId); create index SiCiInMarks on Marks using btree (StudentId, CourseId, Mark);
Хэш-индекс на префикс упорядоченного индекса: create index MarkByStudentIdExists on Marks using hash (StudentId); create index SiAndMark on Marks using btree (StudentId, Mark);
Не unique индекс (а должен): create index SiCiInMarks on Marks using btree (StudentId, CourseId, Mark);
Нет индекса на PK: create unique index on Marks using hash (StudentId, CourseId);
Ожидался покрывающий индекс вместо: create index MarkCourseToStudent on Marks using hash (CourseId, Mark);
Индекс мало/бесполезен: ДЗ-5.3.1 для create index MarkCourseToStudent on Marks using hash (CourseId, Mark);

2.     Средний балл

2.Q. Запрос

2.I. Индексы

Не хватает индекса: create index on Groups using hash (GroupName);
Не хватает индекса: create index on Courses using btree (CourseName, CourseId);

3.     Новые запросы

3.1.Q. Запрос

3.1.I. Индексы

Полезность индекса не очевидна

3.2.Q. Запрос

3.2.I. Индексы

3.3.Q. Запрос

3.3.I. Индексы