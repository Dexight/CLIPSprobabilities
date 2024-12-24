using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Data;
using System.Drawing;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Windows.Forms;
using System.Text.RegularExpressions;

using CLIPSNET;
using System.Data.SqlTypes;
using System.Xml.Linq;


namespace ClipsFormsExample
{
    public partial class ClipsFormsExample : Form
    {
        private CLIPSNET.Environment clips = new CLIPSNET.Environment();

        public ClipsFormsExample()
        {
            InitializeComponent();

        }

        protected override void OnLoad(EventArgs e)
        {
            base.OnLoad(e);
        }

        string end;

        private void HandleResponse()
        {
            //  Вытаскиаваем факт из ЭС
            bool isEnd = false;    
            
            String evalStr = "(find-fact ((?f ioproxy)) TRUE)";
            FactAddressValue fv = (FactAddressValue)((MultifieldValue)clips.Eval(evalStr))[0];

            MultifieldValue damf = (MultifieldValue)fv["messages"];

            outputBox.Text += "\r\nНачало итерации:" + System.Environment.NewLine;
            for (int i = 0; i < damf.Count; i++)
            {
                LexemeValue da = (LexemeValue)damf[i];
                byte[] bytes = Encoding.Default.GetBytes(da.Value);
                string message = Encoding.UTF8.GetString(bytes);

                outputBox.Text += message + "\r\n\r\n";

                string[] message_words = message.Split(' ');
                string proved_fact = message_words[message_words.Length - 2].Trim('<', '>');
                if (proved_fact == end)
                {
                    isEnd = true;
                    break;
                }
            }

            clips.Eval("(assert (clearmessage))");
            if (isEnd)
            {
                outputBox.Text += "Теорема выведена!\r\n";
            }
            else
            {
                outputBox.Text += "Сделали всё что могли! Доказать невозможно.\r\n";
            }
        }

        private void nextBtn_Click(object sender, EventArgs e)
        {
            if (codeBox.Text.Length == 0)
            {
                outputBox.Text += "Выберите файл .clp!\r\n";
                return;
            }

            List<string> init = new List<string>();

            bool isChoosed = false;

            foreach (var item in checkedListBox1.CheckedItems)
            {
                init.Add(item.ToString());
                isChoosed = true;
            }

            if (!isChoosed)
            {
                outputBox.Text += "Выберите стартовые теоремы!\r\n";
                return;
            }

            if (listBox1.SelectedItem == null)
            {
                outputBox.Text += "Выберите целевую теорему!\r\n";
                return;
            }
            else end = listBox1.SelectedItem.ToString();

            Random rand = new Random();
            List<double> coefs = new List<double>();
            outputBox.Text += "Выбор сделан!\r\nДаны следующие теоремы:\r\n";
            foreach (string s in init)
            {
                double c = 0.9;// Math.Round(rand.NextDouble(), 2);
                outputBox.Text += s+$"({c.ToString().Replace(",", ".")})\r\n";
                coefs.Add(c);
            }
            outputBox.Text += "\r\nНужно доказать:\r\n"+end+"(?)\r\n";

            if (init.Contains(end))
            {
                outputBox.Text += "\r\n" + end + " уже и так доказано!";
                return;
            }

            int indx = 0;
            foreach (string s in init)
                clips.Eval($"(assert (theorem (name {s}) (coef {coefs[indx++].ToString().Replace(",", ".")})))");
            clips.Run();
            HandleResponse();
        }

        private void resetBtn_Click(object sender, EventArgs e)
        {
            nextButton.Enabled = true;

            outputBox.Text = "Выполнены команды Clear и Reset." + System.Environment.NewLine;
            //  Здесь сохранение в файл, и потом инициализация через него
            clips.Clear();
            //  Так тоже можно - без промежуточного вывода в файл
            clips.LoadFromString(codeBox.Text);

            clips.Reset();
        }

        HashSet<string> theorems = new HashSet<string>();

        private void openFile_Click(object sender, EventArgs e)
        {
            if (clipsOpenFileDialog.ShowDialog() == DialogResult.OK)
            {
                theorems.Clear();
                checkedListBox1.Items.Clear();
                listBox1.Items.Clear();

                string text = codeBox.Text = System.IO.File.ReadAllText(clipsOpenFileDialog.FileName);
                string pattern = @"\(name\s+([^?\s].*?)\)";

                MatchCollection matches = Regex.Matches(text, pattern);

                foreach (Match match in matches)
                {
                    string substring = match.Groups[1].Value;
                    theorems.Add(substring);
                }

                foreach (string s in theorems)
                {
                    checkedListBox1.Items.Add(s);
                    listBox1.Items.Add(s);
                }

                clips.Clear();
                clips.LoadFromString(codeBox.Text);
                clips.Reset();
            }
        }

        private void fontSelect_Click(object sender, EventArgs e)
        {
            if (fontDialog1.ShowDialog() == DialogResult.OK)
            {
                codeBox.Font = fontDialog1.Font;
                outputBox.Font = fontDialog1.Font;
            }
        }

        private void saveAsButton_Click(object sender, EventArgs e)
        {
            clipsSaveFileDialog.FileName = clipsOpenFileDialog.FileName;
            if (clipsSaveFileDialog.ShowDialog() == DialogResult.OK)
            {
                System.IO.File.WriteAllText(clipsSaveFileDialog.FileName, codeBox.Text);
            }
        }

        private void outputBox_TextChanged(object sender, EventArgs e)
        {

        }

        private void codeBox_TextChanged(object sender, EventArgs e)
        {

        }

        private void panel2_Paint(object sender, PaintEventArgs e)
        {

        }

        private void listBox1_SelectedIndexChanged(object sender, EventArgs e)
        {

        }

        private void checkedListBox1_SelectedIndexChanged(object sender, EventArgs e)
        {

        }
    }
}
